import EinsteinFull.Calculus.C8UnforcedDriftGaussianDecay
import EinsteinFull.Calculus.C1DyadicZeroTranspose

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

theorem c7_dyadic_unforced_initial_average (hlocal : node_e_u3A_forced_u2D_localityStmt) (hends : node_stationary_u2D_analytic_u2D_semigroup_u23_endpointsStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) (T : ℝ) (hT : 0 ≤ T) : ∃ C : ℝ, 1 ≤ C ∧ ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ → ∀ (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)), IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P → IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d, ∀ t : ℝ≥0, (t : ℝ) ≤ T → ∀ s : ℝ, ∀ hs : 0 < s, ‖gaussianAverage hd Q s hs (indexedEndpoint hd Q ν 0 P Pdag β a μ t)‖ ≤ C * s ^ (-(1/2+(d : ℝ)/4)) := by
  obtain ⟨C, hC, hb⟩ := unforced_drift_gaussian_decay hlocal hends d hd D T hT
  refine ⟨max 1 C, le_max_left _ _, ?_⟩
  intro Q hQ β a μ hβ ha hμ P Pdag hP hPd ν t ht s hs
  let F := fun z => forcedComplexEvolution Q (⟨0, by omega⟩ : Fin d) z
  let Fdag := fun z r => complexL2Transpose (reducedLaw Q) (F z r)
  have hF : ∀ z, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ z (F z) :=
    fun z => isComplexEnvironmentSemigroup_forcedComplexEvolution Q _ z
  have hFd : ∀ z, IsComplexTransposeSemigroup Q (F z) (Fdag z) :=
    fun z => isComplexTransposeSemigroup_complexL2Transpose Q (F z)
  have he : F 0 = P := (hF 0).unique hP
  have hdg : Pdag = P := c1_dyadic_zero_transpose_eq P Pdag hP hPd
  have hbound (j : Fin d) : ‖gaussianAverage hd Q s hs (P t (β j))‖ ≤
      max 1 C * s ^ (-(1/2+(d : ℝ)/4)) := by
    have h := hb Q hQ β a μ hβ ha hμ F Fdag hF hFd t ht j s hs
    rw [he] at h
    exact h.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.rpow_nonneg hs.le _))
  cases ν with
  | inl j =>
    simpa only [indexedEndpoint, velocityEndpoint, zero_smul, add_zero,
      c8_centered_unforced_drift hd hβ hP hPd] using hbound j
  | inr b =>
    cases b with
    | false =>
      simp only [indexedEndpoint, clockEndpoint, zero_smul]
      have hz : gaussianAverage hd Q s hs 0 = 0 := by
        simp [gaussianAverage]
      rw [hz, norm_zero]
      exact mul_nonneg (le_trans (by norm_num) (le_max_left 1 C)) (Real.rpow_nonneg hs.le _)
    | true =>
      simpa only [indexedEndpoint, transposeEndpoint, hdg] using hbound ⟨0, by omega⟩

end EinsteinFull.Blueprint
