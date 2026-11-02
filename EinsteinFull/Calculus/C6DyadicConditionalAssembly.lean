import EinsteinFull.Calculus.C6DyadicIncrementsRoot
import EinsteinFull.Calculus.C3DyadicDensityDecayTransfer
import EinsteinFull.Blueprint.G3.node_p_u3A_late_u23_dyadic_u2D_increments

open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Assemble the dyadic increment estimates from a uniform density increment bound. -/
theorem c6_dyadic_increments_of_density_increment_bound (hdensity : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C : ℝ, 1 ≤ C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
    ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag →
    ∀ s u : ℝ≥0, 1 ≤ (s : ℝ) → s ≤ u → u ≤ 2 * s →
      ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2 →
    let := reducedLaw_probability Q
    ‖Pdag u (Lp.const 2 (reducedLaw Q) 1) - Pdag s (Lp.const 2 (reducedLaw Q) 1)‖ ≤
      C * (s : ℝ) ^ (-(d : ℝ) / 4)) (henergy : node_e_u3A_energy_u2D_targetStmt) (hlocal : node_l_u3A_forced_u2D_localStmt) (hflux : node_e_u3A_time_u2D_fluxStmt) : node_p_u3A_late_u23_dyadic_u2D_incrementsStmt := by
  intro d hd D
  obtain ⟨C₀, c, N, hC₀, hc, hdata⟩ :=
    c6_dyadic_increments_data_of_deps henergy hlocal hflux d hd D
  obtain ⟨C₂, hC₂, hdens⟩ := hdensity d hd D
  let A : ℝ := (d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity)
  let C := max C₀ (A * C₂)
  have h₀ : C₀ ≤ C := le_max_left _ _
  have hA : A * C₂ ≤ C := le_max_right _ _
  have hC : 1 ≤ C := hC₀.trans h₀
  refine ⟨C, c, N, hC, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd
  obtain ⟨G, F, hF, hfirst, hdyadic⟩ :=
    hdata Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd
  refine ⟨G, F, hF, ?_, ?_⟩
  · intro hζ ν
    obtain ⟨hsize, hlocality⟩ := hfirst hζ ν
    refine ⟨hsize.trans h₀, ?_⟩
    intro n hn
    obtain ⟨V, hV, herror⟩ := hlocality n hn
    refine ⟨V, ?_, herror.trans ?_⟩
    · intro j
      obtain ⟨v, hv, hveq⟩ := hV j
      refine ⟨v, hv.mono (Probability.localSigma_mono ?_) le_rfl, hveq⟩
      intro x hx
      exact lt_of_lt_of_le hx (mul_le_mul_of_nonneg_right h₀ (Nat.cast_nonneg n))
    · exact mul_le_mul_of_nonneg_right h₀ (Real.exp_nonneg _)
  intro s u hs hsu hus hζ ν
  obtain ⟨Y, B, hY, hB, hsplit, hsize, hBeq, _hprimitive, hlocality⟩ :=
    hdyadic s u hs hsu hus hζ ν
  refine ⟨Y, B, hY, hB, hsplit, hsize.trans ?_, ?_, ?_⟩
  · exact mul_le_mul_of_nonneg_right h₀ (Real.rpow_nonneg s.coe_nonneg _)
  · simp_rw [hBeq]
    cases ν with
    | inl ν =>
      simp only [Sum.elim_inl, norm_zero, zero_pow (by decide : (2 : ℕ) ≠ 0),
        Finset.sum_const_zero, Real.sqrt_zero]
      exact mul_nonneg (zero_le_one.trans hC) (Real.rpow_nonneg s.coe_nonneg _)
    | inr ν =>
      simp only [Sum.elim_inr]
      have hb := c3_actual_flux_decay_of_density_bound hβ hP hPd s u hsu C₂
        (hdens Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd s u hs hsu hus hζ)
      calc
        _ ≤ A * (C₂ * (s : ℝ) ^ (-(d : ℝ) / 4)) := hb
        _ = (A * C₂) * (s : ℝ) ^ (-(d : ℝ) / 4) := by ring
        _ ≤ C * (s : ℝ) ^ (-(d : ℝ) / 4) :=
          mul_le_mul_of_nonneg_right hA (Real.rpow_nonneg s.coe_nonneg _)
  · intro n hn
    obtain ⟨V, hV, herror⟩ := hlocality n hn
    have hR : C₀ * n * Real.sqrt (s : ℝ) ≤ C * n * Real.sqrt (s : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₀ (Nat.cast_nonneg n))
        (Real.sqrt_nonneg _)
    refine ⟨V, ?_, herror.trans ?_⟩
    · intro j
      obtain ⟨v, hv, hveq⟩ := hV j
      refine ⟨v, hv.mono (Probability.localSigma_mono ?_) le_rfl, hveq⟩
      intro x hx
      exact lt_of_lt_of_le hx hR
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h₀ (pow_nonneg (by positivity) N))
        (Real.exp_nonneg _)

end EinsteinFull.Blueprint
