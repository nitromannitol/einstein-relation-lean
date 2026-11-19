import EinsteinFull.Regeneration.ReducedCenteredSurvival
import EinsteinFull.Calculus.C10S3StoppedTubeProducer

/-!
# Uniform regeneration guard estimate

The reduced diffusion's centered survival estimate yields a positive conditional
probability of each guard at its actual passage, uniformly over the past history.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration EinsteinFull.Blueprint
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The literal failed-guard history has a uniformly positive chance of a good
passage at the next selected even trial. -/
theorem guard_estimate {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧
      ∀ (m : ℕ) (A : CoupledSample d → ℝ),
        @Measurable (CoupledSample d) ℝ
          (finiteHistorySigma (Renewal.regenDelta lam) m) inferInstance A →
      ∀ N : ℕ,
        let Δ := Renewal.regenDelta lam
        let R := l / lam
        let i := Renewal.forceCoord hd
        let μ := annealedCoupledLaw Q.measure K
        let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩
          {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}
        ε * μ.real E ≤ μ.real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N}) := by
  obtain ⟨ε, hε, hε1, htube⟩ := reduced_centered_survival hd Λ₀ r₀ l hl
  refine ⟨ε, hε, hε1, ?_⟩
  intro m A hA N
  let μ := annealedCoupledLaw Q.measure K
  let : IsProbabilityMeasure Q.measure := Q.probability
  let : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hbase := htube Q lam (by simpa only [abs_of_pos h0] using h0)
    (by simpa only [abs_of_pos h0] using h1) P (by
      simpa only [abs_of_pos h0] using hK.2.2.1)
  have htube' := c10_s3_stopped_tube_of_uniform_quenched_tube hd Q lam h0 h1
    l δ hl hsep hδ0 hδ1 P K hK ε hε (by
      simpa only [abs_of_pos h0] using hbase) m A hA N
  exact coupling_scope_guard_estimate_of_tube_estimate μ (Renewal.regenDelta lam)
    (EinsteinRelation.regenDelta_pos h0) lam (l / lam) ε A m (Renewal.forceCoord hd) N htube'

end EinsteinFull.Regeneration
