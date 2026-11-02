import EinsteinFull.Calculus.C1DyadicPointMajorantFinite

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

/-- The maximum of one and the supremum of the endpoint norms normalized by
the exponential and pointwise decay weight, over times in `[1, T]`. -/
noncomputable def dyadicPointMajorant (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (ν : EndpointIndex d) (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)) (growth T : ℝ) : ℝ := max 1 (sSup {z : ℝ | ∃ t : ℝ≥0, 1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ T ∧ z = ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ / (Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4)))})

/-- The maximum of one and the supremum of Gaussian-average endpoint norms
normalized by the exponential and spatial decay weight, over times in `[1, T]`
and positive averaging scales `s` satisfying `b * t ≤ s`. -/
noncomputable def dyadicAverageMajorant (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (ν : EndpointIndex d) (ζ : ℂ) (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)) (b growth T : ℝ) : ℝ := max 1 (sSup {z : ℝ | ∃ t : ℝ≥0, ∃ s : ℝ, ∃ hs : 0 < s, 1 ≤ (t : ℝ) ∧ (t : ℝ) ≤ T ∧ b*(t : ℝ) ≤ s ∧ z = ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ / (Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) * ((s) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (s) ^ (-(d : ℝ)/4)))})

theorem c1_dyadic_named_point_majorant_bounds (hlocal : node_l_u3A_forced_u2D_localStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 1 ≤ T) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ‖ζ‖ ≤ 2 → ∀ growth : ℝ, 0 ≤ growth → 1 ≤ dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth T ∧ dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth T ≤ C ∧ ∀ t : ℝ≥0, 1 ≤ (t : ℝ) → (t : ℝ) ≤ T → ‖indexedEndpoint hd Q ν ζ P Pdag β a μ t‖ ≤ dyadicPointMajorant d hd D Q ν ζ P Pdag β a μ growth T * (Real.exp (growth * ‖ζ‖^2 * (t : ℝ)) * ((t : ℝ) ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ)/4))) := by
  obtain ⟨C, hC, hbound⟩ := c1_dyadic_actual_point_majorant_finite hlocal d hd D T hT
  refine ⟨C, hC, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ growth hgrowth
  obtain ⟨_, _, _, hsup, hpoint⟩ := hbound Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν hζ growth hgrowth
  refine ⟨le_max_left _ _, max_le hC hsup, ?_⟩
  intro t ht htT
  exact (hpoint t ht htT).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))

end EinsteinFull.Blueprint
