import EinsteinFull.Calculus.C19FirstUnitGradientProjection
import EinsteinFull.Calculus.C8DyadicLargeWindowFluxLocality
import EinsteinFull.Calculus.C7DyadicFluxDecomposition
import EinsteinFull.Blueprint.G3.node_p_u3A_late_u23_dyadic_u2D_increments

/-! Assembly of the checked estimates on the same supplied finite-time flux.

The full dyadic-increments root still needs the first-unit flux locality and
the full-window transpose size estimate. Neither is assumed by this support
theorem, which records only the conclusions already available from producers.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- A single structural constant controls the first-unit size, the actual
dyadic gradient flux and the joint-local dyadic approximants. The exact
transpose term is retained for the remaining size estimate. -/
theorem c6_dyadic_gradient_flux_decomposition_and_locality
    (henergy : node_e_u3A_energy_u2D_targetStmt)
    (hlocal : node_l_u3A_forced_u2D_localStmt) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
      ∃ C c : ℝ, ∃ N : ℕ, 1 ≤ C ∧ 0 < c ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
        IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
        IsComplexTransposeSemigroup Q P Pdag →
      ∀ G F : ℝ≥0 → FluxIndex d → Fin d → Lp ℂ 2 (reducedLaw Q),
        IsFiniteTimeFlux hd Q ζ P Pdag β a μ G F →
      (‖ζ‖ ≤ 2 → ∀ ν : FluxIndex d,
        Real.sqrt (∑ j : Fin d, ‖F 1 ν j - F 0 ν j‖ ^ 2) ≤ C) ∧
      ∀ s u : ℝ≥0, 1 ≤ (s : ℝ) → s ≤ u → u ≤ 2 * s →
        ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) ≤ 2 → ∀ ν : FluxIndex d,
      ∃ Y B : Fin d → Lp ℂ 2 (reducedLaw Q),
        (∀ j, (Y j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          fun ω => ∑ k : Fin d, a j k ω *
            (∫ r in Set.Icc (s : ℝ) (u : ℝ), G r.toNNReal ν k) ω) ∧
        (∀ j, (B j : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
          fun ω => ν.elim (fun _ => 0) (fun _ =>
            -2 * ζ * a j ⟨0, by omega⟩ ω *
              (∫ r in Set.Icc (s : ℝ) (u : ℝ),
                transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal) ω)) ∧
        (∀ j, F u ν j - F s ν j = Y j + B j) ∧
        Real.sqrt (∑ j : Fin d, ‖Y j‖ ^ 2) ≤ C * (s : ℝ) ^ (-(d : ℝ) / 4) ∧
        (∀ j, B j = ν.elim (fun _ => 0) (fun _ => (-2 * ζ) •
          complexCoefficientMul Q j ⟨0, by omega⟩
            (∫ r in Set.Icc (s : ℝ) (u : ℝ),
              transposeEndpoint Q ⟨0, by omega⟩ Pdag β r.toNNReal))) ∧
        ∀ n : ℕ, 1 ≤ n → ∃ V : Fin d → Lp ℂ 2 (reducedLaw Q),
          (∀ j, IsComplexLocalObservation Q (C * n * Real.sqrt (s : ℝ)) (V j)) ∧
          Real.sqrt (∑ j : Fin d, ‖F u ν j - F s ν j - V j‖ ^ 2) ≤
            C * (2 + (s : ℝ)) ^ N * Real.exp (-c * (n : ℝ) ^ 2) := by
  intro d hd D
  obtain ⟨C₁, hC₁, hfirst⟩ := first_unit_flux_size d hd D
  obtain ⟨C₂, _hC₂, hgradient⟩ := dyadic_integrated_gradient_flux_size henergy d hd D
  obtain ⟨C₃, c, N, hC₃, hc, hlocality⟩ :=
    dyadic_large_window_flux_locality (c19_dyadic_locality_input_of_forced_local hlocal) d hd D
  let C := max C₁ (max C₂ C₃)
  have h₁ : C₁ ≤ C := le_max_left _ _
  have h₂ : C₂ ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have h₃ : C₃ ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  refine ⟨C, c, N, hC₁.trans h₁, hc, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF
  refine ⟨fun hζ ν => (hfirst Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF hζ ν).trans h₁,
    ?_⟩
  intro s u hs hsu hus hζ ν
  obtain ⟨Y, B, hY, hB, hsplit, hYeq, hBeq⟩ :=
    dyadic_flux_decomposition hd Q ζ P Pdag β a μ ha G F hF s u hsu ν
  refine ⟨Y, B, hY, hB, hsplit, ?_, hBeq, ?_⟩
  · simp_rw [hYeq]
    exact (hgradient Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF
      s u hs hsu hus hζ ν).trans
      (mul_le_mul_of_nonneg_right h₂ (Real.rpow_nonneg s.coe_nonneg _))
  · intro n hn
    obtain ⟨V, hV, herror⟩ := hlocality Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd G F hF
      s u hs hsu hus hζ ν n hn
    have hR : C₃ * n * Real.sqrt (s : ℝ) ≤ C * n * Real.sqrt (s : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h₃ (Nat.cast_nonneg n))
        (Real.sqrt_nonneg _)
    refine ⟨V, ?_, herror.trans ?_⟩
    · intro j
      obtain ⟨v, hv, hveq⟩ := hV j
      refine ⟨v, hv.mono (Probability.localSigma_mono ?_) le_rfl, hveq⟩
      intro x hx
      exact lt_of_lt_of_le hx hR
    · exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right h₃ (pow_nonneg (by positivity) N))
        (Real.exp_nonneg _)

end EinsteinFull.Blueprint
