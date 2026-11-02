import EinsteinFull.Calculus.C6FluxGrowthAbsorption

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Assemble the two event estimates for the same translated flux block. -/
theorem c6_actual_flux_block_event_assembly
    (d : ℕ) (κ C Cp : ℝ) (hκ : 0 < κ) (hκhalf : κ < 1 / 2)
    (hC : 0 ≤ C) (hCp : 0 ≤ Cp) :
    ∃ A growth₀ : ℝ, 1 ≤ A ∧ 0 < growth₀ ∧
    ∀ growth : ℝ, growth₀ ≤ growth →
    ∀ (t : ℝ≥0) (ζ : ℂ), 1 ≤ (t : ℝ) →
    ∀ (p : ℝ), 1 ≤ p → ∀ (Λ r₀ : ℝ) (Q : EnvironmentLaw d Λ r₀)
      (ψ : Vec d → ℂ) (J : Lp ℂ 2 (reducedLaw Q))
      (E : Set (FieldPair d)), MeasurableSet E →
    ∀ H K : ℝ, 0 ≤ H → 1 ≤ K →
    let η := κ / (16 * ((d : ℝ) + 2))
    let r := (t : ℝ) ^ (1 / 2 + η)
    let R := 2 * Real.sqrt (d : ℝ) + 3
    let B : Lp ℂ 2 (reducedLaw Q) := ∫ y : Vec d,
      ψ y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J
    MemLp (E.indicator (B : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp (Eᶜ.indicator (B : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) →
    (eLpNorm (E.indicator (B : FieldPair d → ℂ))
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      H * K * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        (R * r) ^ ((d : ℝ) + 1 - κ) *
        (1 + ‖ζ‖ * Real.sqrt (t : ℝ)) ^ C *
        Real.exp (Cp * ‖ζ‖ ^ 2 * (t : ℝ)) *
        Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) →
    (eLpNorm (Eᶜ.indicator (B : FieldPair d → ℂ))
      (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      H * (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) →
    MemLp (B : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
    (eLpNorm (B : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤
      A * H * K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
        (t : ℝ) ^ (-1 - (1 / 2 + (d : ℝ) / 4)) *
        r ^ ((d : ℝ) + 1 - κ) := by
  obtain ⟨A, growth₀, hA, hg₀, hbudget⟩ :=
    c6_flux_selected_radius_final_budget d κ C Cp hκ hκhalf hC hCp
  refine ⟨A, growth₀, hA, hg₀, ?_⟩
  intro growth hg t ζ ht p hp Λ r₀ Q ψ J E hE H K hH hK
  dsimp only
  intro hgood hbad hgoodbound hbadbound
  let B : Lp ℂ 2 (reducedLaw Q) := ∫ y : Vec d,
    ψ y • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y J
  have heq : E.indicator (B : FieldPair d → ℂ) + Eᶜ.indicator (B : FieldPair d → ℂ) = B := by
    ext ω
    by_cases hω : ω ∈ E <;> simp [hω]
  have hp1 : 1 ≤ ENNReal.ofReal p := by simpa using ENNReal.ofReal_le_ofReal hp
  have hmem := hgood.add hbad
  rw [heq] at hmem
  refine ⟨hmem, ?_⟩
  have htri := eLpNorm_add_le (f := E.indicator (B : FieldPair d → ℂ))
    (g := Eᶜ.indicator (B : FieldPair d → ℂ)) (μ := reducedLaw Q) hp1
  rw [heq] at htri
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hgood.eLpNorm_ne_top, hbad.eLpNorm_ne_top⟩) htri
  rw [ENNReal.toReal_add hgood.eLpNorm_ne_top hbad.eLpNorm_ne_top] at hreal
  have hb := hbudget growth hg t ζ ht H K hH hK
  dsimp only at hb
  linarith

end EinsteinFull.Blueprint
