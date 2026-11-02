import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation Regeneration ProbabilityTheory

/-- Finite passages at every shifted level and integrated guard estimates give
finite trial entries at every starting grid on the supplied coupled law. -/
theorem c14_s3_entries_of_finite_passages_and_guards
    {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hFresh : HasFreshBits Q Δ δ K) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R) (i : Fin d)
    (hpass : ∀ᵐ q ∂annealedCoupledLaw Q K, ∀ (s : ℝ≥0) (a : ℝ) (n : ℕ),
      passageSequence Δ lam R a (pathTimeShift q.2.1 s) i n ≠ ⊤)
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hwin : ∀ (m : ℕ) (A : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance A → ∀ N,
      let μ := annealedCoupledLaw Q K
      let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
        {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
      ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N})) :
    let μ := annealedCoupledLaw Q K
    ∀ᵐ q ∂μ, ∀ m : ℕ,
      let w := sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
      trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧
        ∀ n, trialFailureTime Δ R w i (trialStartSequence Δ lam R w i n) ≠ ⊤ →
          trialStartSequence Δ lam R w i (n + 1) ≠ ⊤ := by
  apply coupling_scope_ae_all_grid_trial_entries_of_successful_candidates
    (annealedCoupledLaw Q K) Δ hΔ lam R i
  intro m A hA
  apply coupling_scope_ae_successful_candidate_finite_of_guard_estimates
    Q K hK Δ hΔ δ hδ hδ1 hFresh lam R hlam hR i ε hε hε1 _ hwin m A hA
  intro m' A' _hA'
  filter_upwards [hpass] with q hq n
  exact hq ((m' : ℝ≥0) * Δ) (A' q.2) n

end EinsteinFull.Blueprint
