import EinsteinFull.Calculus.C7BoundedTimeGaussianForceDifference
import EinsteinFull.Calculus.C7DyadicUnforcedInitialization

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

theorem c4_dyadic_bounded_time_initial_average (hlocal : node_e_u3A_forced_u2D_localityStmt) (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ ζ : ℂ, ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ‖ζ‖ ≤ 2 → ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ s : ℝ, ∀ hs : 0 < s, ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t)‖ ≤ C * (s ^ (-(1/2+(d : ℝ)/4)) + ‖ζ‖ * s ^ (-(d : ℝ)/4)) := by
  obtain ⟨C₀, hC₀, hzero⟩ := c7_dyadic_unforced_initial_average hlocal hends d hd D T hT
  obtain ⟨C₁, hC₁, hdiff⟩ := bounded_time_gaussian_force_difference hlocal hends d hd D T 2 hT (by norm_num)
  refine ⟨max C₀ C₁, le_trans hC₀ (le_max_left _ _), ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν hζ t ht s hs
  let P₀ := forcedComplexEvolution Q ⟨0, by omega⟩ 0
  let P₀dag := fun u => complexL2Transpose (reducedLaw Q) (P₀ u)
  let U₀ := indexedEndpoint hd Q ν 0 P₀ P₀dag β a μ t
  have hz := hzero Q hQ β a μ hβ ha hμ P₀ P₀dag
    (isComplexEnvironmentSemigroup_forcedComplexEvolution Q _ 0)
    (isComplexTransposeSemigroup_complexL2Transpose Q P₀) ν t ht s hs
  have hf := (hdiff Q hQ β a μ hβ ha hμ ζ P Pdag hP hPd ν hζ t ht s hs).2
  change (eLpNorm (gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t - U₀) : FieldPair d → ℂ) (ENNReal.ofReal 2) (reducedLaw Q)).toReal ≤ _ at hf
  have hf' : ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t - U₀)‖ ≤ C₁ * ‖ζ‖ * s ^ (-(d : ℝ)/4) := by
    rw [Lp.norm_def]
    simpa using hf
  have hsub : gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t - U₀) = gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t) - gaussianAverage hd Q s hs U₀ := by
    change homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0 (_ - _) = _
    exact map_sub _ _ _
  rw [hsub] at hf'
  change ‖gaussianAverage hd Q s hs U₀‖ ≤ _ at hz
  have ht' := norm_sub_le (gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t)) (gaussianAverage hd Q s hs U₀)
  have hx : 0 ≤ s ^ (-(1/2+(d : ℝ)/4)) := Real.rpow_nonneg hs.le _
  have hy : 0 ≤ ‖ζ‖ * s ^ (-(d : ℝ)/4) := mul_nonneg (norm_nonneg _) (Real.rpow_nonneg hs.le _)
  have hc₀ := mul_le_mul_of_nonneg_right (le_max_left C₀ C₁) hx
  have hc₁ := mul_le_mul_of_nonneg_right (le_max_right C₀ C₁) hy
  have htri := norm_add_le (gaussianAverage hd Q s hs (indexedEndpoint hd Q ν ζ P Pdag β a μ t) - gaussianAverage hd Q s hs U₀) (gaussianAverage hd Q s hs U₀)
  simp only [sub_add_cancel] at htri
  nlinarith

end EinsteinFull.Blueprint
