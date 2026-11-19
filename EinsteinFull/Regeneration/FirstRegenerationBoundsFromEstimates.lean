import EinsteinFull.Regeneration.FirstRegenerationTailReduction
import EinsteinFull.Regeneration.NoReturnFromHitting
import EinsteinFull.Frozen.RegenerationTime
import EinsteinRelation.Regeneration.RenewalRecordIteration

/-!
# First-regeneration bounds from hitting and endpoint estimates

The no-return and time-tail conclusions of Gantert–Mathieu–Piatnitski, Lemma 5.8, follow
from the corresponding quenched hitting estimates, finiteness and an exponential endpoint
moment. These source-specific estimates remain explicit hypotheses.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The literal no-return and first-time bounds follow from the source hitting estimates
and the integrable exponential endpoint moment. -/
theorem first_regeneration_bounds_of_estimates {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : EinsteinFull.IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (κ s C D : ℝ) (hC : 0 < C) (hD : 0 < D) (hs : 0 ≤ s)
    (hback : ∀ᵐ ω ∂Q.measure, P (0, ω) {γ |
      firstHittingBelow γ (Regeneration.Renewal.forceCoord hd) (-(l / lam)) ≠ ⊤} ≤
        ENNReal.ofReal (1 / 2 : ℝ))
    (hhit : ∀ (T : ℝ≥0) (a : ℝ), ∀ᵐ ω ∂Q.measure,
      P (0, ω) {γ | (T : ℝ≥0∞) ≤ firstHittingAbove γ (Regeneration.Renewal.forceCoord hd) a} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam ^ 2 * T + lam * a)))
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) ωz.2
        (Regeneration.Renewal.forceCoord hd) ≠ ⊤)
    (hint : Integrable (fun ωz : FieldPair d × CoupledSample d =>
      Real.exp (s * (lam * (ωz.2.1 (firstRegenerationTime (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) ωz.2 (Regeneration.Renewal.forceCoord hd)).toNNReal
          (Regeneration.Renewal.forceCoord hd) - ωz.2.1 0 (Regeneration.Renewal.forceCoord hd)))))
      (annealedCoupledLaw Q.measure K))
    (hmoment : (∫ ωz : FieldPair d × CoupledSample d,
      Real.exp (s * (lam * (ωz.2.1 (firstRegenerationTime (Regeneration.Renewal.regenDelta lam)
        lam (l / lam) ωz.2 (Regeneration.Renewal.forceCoord hd)).toNNReal
          (Regeneration.Renewal.forceCoord hd) - ωz.2.1 0 (Regeneration.Renewal.forceCoord hd))))
      ∂annealedCoupledLaw Q.measure K) ≤ D) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤ annealedCoupledLaw Q.measure K (EinsteinFull.regenerationNoReturn hd (l / lam)) ∧
    ∀ t : ℝ, 0 ≤ t →
      annealedCoupledLaw Q.measure K {ωz | ENNReal.ofReal t < EinsteinFull.regenerationTime hd lam l 1 ωz.2} ≤
        ENNReal.ofReal ((C + D * Real.exp (12 * s * l)) *
          Real.exp (-(min (κ / 2) (s * κ / 2)) * lam ^ 2 * t)) := by
  have : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨hprob, hpath, _, _, _, hsupport, _, _⟩ := hK
  refine ⟨no_return_mass_of_backtracking_bound hd Q.measure P K hprob hpath (l / lam) hback, ?_⟩
  intro t ht
  have hEnd := first_regeneration_endpoint_tail_of_exp_moment Q.measure K hprob
    (Regeneration.Renewal.regenDelta lam) lam (l / lam) (Regeneration.Renewal.forceCoord hd)
    s D hs hint hmoment
  have hHit := annealed_forward_hitting_bound Q.measure P K hprob hpath lam κ C
    (Regeneration.Renewal.forceCoord hd) hhit
  have htail := first_regeneration_tail_of_hitting_and_endpoint Q.measure K hprob
    (Regeneration.Renewal.regenDelta lam) (EinsteinRelation.regenDelta_pos h₀)
    lam l h₀ hl (Regeneration.Renewal.forceCoord hd) hsupport hfinite κ s C D hC hD hHit hEnd t.toNNReal
  simpa only [EinsteinFull.regenerationTime, Regeneration.regenerationTime_one,
    ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ ht] using htail

end EinsteinFull.Regeneration
