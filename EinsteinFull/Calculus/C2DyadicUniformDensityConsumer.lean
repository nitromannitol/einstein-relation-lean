import EinsteinFull.Calculus.C2DyadicDensityFromEndpoint

open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- A uniform endpoint estimate supplies the uniform density increment bound. -/
theorem c2_dyadic_density_of_uniform_endpoint_decay (hendpoint : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d), ∃ A : ℝ, 1 ≤ A ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → ‖ζ‖ * Real.sqrt (t : ℝ) ≤ 2 → ‖transposeEndpoint Q ⟨0, by omega⟩ Pdag β t‖ ≤ A * (t : ℝ) ^ (-(1/2+(d : ℝ)/4))) : ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
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
      C * (s : ℝ) ^ (-(d : ℝ) / 4) := by
  intro d hd D
  obtain ⟨A, hA, hend⟩ := hendpoint d hd D
  let B : ℝ := 4 * Real.exp (2 * (Real.exp (2 * D.ellipticity) * D.ellipticity) *
    ((d : ℝ) * (Real.exp (2 * D.ellipticity) * D.ellipticity)) ^ 2) * A
  refine ⟨max 1 B, le_max_left _ _, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd s u hs hsu hus hz
  have hspos : 0 < (s : ℝ) := by linarith
  have hforce : ‖ζ‖ * Real.sqrt (s : ℝ) ≤ 2 := by
    calc
      _ ≤ ‖ζ‖ * Real.sqrt (2 * (s : ℝ)) :=
        mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (by linarith [s.coe_nonneg])) (norm_nonneg _)
      _ ≤ 2 := hz
  have hb := c2_dyadic_density_increment_of_endpoint_decay hβ hP hPd s u hspos hsu hus hz A
    (by linarith) (hend Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd s hs hforce)
  exact hb.trans (mul_le_mul_of_nonneg_right (le_max_right 1 B)
    (Real.rpow_nonneg s.coe_nonneg _))

end EinsteinFull.Blueprint
