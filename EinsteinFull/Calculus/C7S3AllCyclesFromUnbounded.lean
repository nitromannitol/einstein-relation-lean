import EinsteinFull.Calculus.C2S3UnboundedPassages
import EinsteinFull.Calculus.C14S3EntriesFromPassages
import EinsteinFull.Calculus.C15S3BurnFromUnbounded
import EinsteinFull.Calculus.C4S3BurnExhaustionAssembly

open EinsteinRelation Regeneration MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

/-- Unbounded excursions and guard contraction give finite regeneration cycles. -/
theorem c7_s3_all_cycles_finite_of_unbounded_and_guard_contraction
    {d : ℕ} (hd : 2 ≤ d) (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (lam l : ℝ) (hlam : 0 < lam) (hl : 0 < l)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hFresh : HasFreshBits Q (Renewal.regenDelta lam) δ K)
    (hunbounded : ∀ᵐ q ∂annealedCoupledLaw Q K, ∀ B : ℝ, ∃ t : ℝ≥0,
      B ≤ q.2.1 t (Renewal.forceCoord hd) - q.2.1 0 (Renewal.forceCoord hd))
    (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hwin : ∀ (m : ℕ) (A : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A → ∀ N,
      let Δ := Renewal.regenDelta lam
      let μ := annealedCoupledLaw Q K
      let E := couplingScopeEvenGuardFailure Δ lam (l / lam) A m (Renewal.forceCoord hd) Set.univ N ∩
        {q | couplingScopePassage Δ lam (l / lam) A m (Renewal.forceCoord hd) (2 * N) q.2 ≠ ⊤}
      ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam (l / lam) A m (Renewal.forceCoord hd) N}))
    (η : ℝ) (hη : 0 < η)
    (hstep : ∀ m J N,
      let Δ := Renewal.regenDelta lam
      let μ := annealedCoupledLaw Q K
      μ (couplingScopeTrialLost Δ lam (l / lam) m (Renewal.forceCoord hd) J (N + 1)) ≤
        ENNReal.ofReal (1 - η) * μ (couplingScopeTrialLost Δ lam (l / lam) m (Renewal.forceCoord hd) J N)) :
    ∀ᵐ q ∂annealedCoupledLaw Q K, ∀ k : ℕ, regenerationTime hd lam l k q.2 ≠ ⊤ := by
  let : IsProbabilityMeasure (annealedCoupledLaw Q K) :=
    annealedCoupledLaw_isProbabilityMeasure Q K hK
  have hΔ : 0 < Renewal.regenDelta lam := EinsteinRelation.regenDelta_pos hlam
  have hpass : ∀ᵐ q ∂annealedCoupledLaw Q K, ∀ (s : ℝ≥0) (a : ℝ) (n : ℕ),
      passageSequence (Renewal.regenDelta lam) lam (l / lam) a
        (pathTimeShift q.2.1 s) (Renewal.forceCoord hd) n ≠ ⊤ := by
    filter_upwards [hunbounded] with q hq s a n
    exact c2_s3_shifted_passages_finite_of_unbounded _ _ _ _ _ hq s a n
  have hentry := c14_s3_entries_of_finite_passages_and_guards Q K hK
    (Renewal.regenDelta lam) hΔ δ hδ hδ1 hFresh lam (l / lam) hlam
    (div_pos hl hlam) (Renewal.forceCoord hd) hpass ε hε hε1 hwin
  have hburn : ∀ᵐ q ∂annealedCoupledLaw Q K, ∀ m : ℕ,
      (∀ n, trialStartSequence (Renewal.regenDelta lam) lam (l / lam)
        (sampleTimeShift (Renewal.regenDelta lam) q.2
          ((m : ℝ≥0) * Renewal.regenDelta lam)) (Renewal.forceCoord hd) n ≠ ⊤) →
      ∃ J, q ∈ couplingScopeTrialBurn (Renewal.regenDelta lam) lam (l / lam)
        m (Renewal.forceCoord hd) J := by
    filter_upwards [hunbounded] with q hq m hfinite
    exact c15_s3_burn_of_unbounded_excursions _ hΔ lam (l / lam) hlam
      (div_pos hl hlam) m (Renewal.forceCoord hd) q hq hfinite
  have hgrid := c4_s3_all_grid_finite_of_burn_and_entries (annealedCoupledLaw Q K)
    (Renewal.regenDelta lam) hΔ lam (l / lam)
    (Renewal.forceCoord hd) hentry hburn η hη hstep
  exact coupling_scope_ae_finite_of_grid_exhaustion hd lam l hlam
    (annealedCoupledLaw Q K) (ae_all_iff.mp hgrid)

end EinsteinFull.Blueprint
