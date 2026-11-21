import EinsteinFull.Regeneration.UniformReturnAtGrid
import EinsteinFull.Regeneration.FirstRegenerationFiniteness
import EinsteinFull.Regeneration.FirstRegenerationTailReduction
import EinsteinFull.Frozen.RegenerationTime

/-!
# Regeneration bounds from hitting and endpoint moments

The estimates of Gantert–Mathieu–Piatnitski, Lemmas 4.1–4.2 and (5.26),
imply the no-return and first-regeneration time bounds of Lemma 5.8.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Uniform no-backtracking, forward hitting, and an exponential endpoint moment imply
both the no-return mass and the first-regeneration time tail. -/
theorem first_regeneration_bounds_of_hitting_and_moment {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (κ s C D : ℝ) (hκ : 0 < κ) (hs : 0 < s) (hC : 0 < C) (hD : 0 < D)
    (hback : ∀ᵐ ω ∂Q.measure, ∀ x, ENNReal.ofReal (1 / 2 : ℝ) ≤
      P (x, ω) {γ | NoBacktracking (l / lam) γ (Renewal.forceCoord hd)})
    (hhit : ∀ (T : ℝ≥0) (a : ℝ), 0 ≤ a → ∀ᵐ ω ∂Q.measure,
      P (0, ω) {γ | (T : ℝ≥0∞) ≤ firstHittingAbove γ (Renewal.forceCoord hd) a} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam ^ 2 * T + lam * a)))
    (hint : Integrable (fun q : FieldPair d × CoupledSample d =>
      Real.exp (s * (lam * (q.2.1 (firstRegenerationTime (Renewal.regenDelta lam)
        lam (l / lam) q.2 (Renewal.forceCoord hd)).toNNReal (Renewal.forceCoord hd) -
          q.2.1 0 (Renewal.forceCoord hd))))) (annealedCoupledLaw Q.measure K))
    (hmoment : (∫ q : FieldPair d × CoupledSample d,
      Real.exp (s * (lam * (q.2.1 (firstRegenerationTime (Renewal.regenDelta lam)
        lam (l / lam) q.2 (Renewal.forceCoord hd)).toNNReal (Renewal.forceCoord hd) -
          q.2.1 0 (Renewal.forceCoord hd)))) ∂annealedCoupledLaw Q.measure K) ≤ D) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤ annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ∧
    ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧ ∀ t : ℝ, 0 ≤ t →
      annealedCoupledLaw Q.measure K {q | ENNReal.ofReal t < regenerationTime hd lam l 1 q.2} ≤
        ENNReal.ofReal (C' * Real.exp (-c * lam ^ 2 * t)) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  have hreturn := trial_return_estimate_of_uniform_no_backtracking hd Q lam h0 h1 l δ hl
    P K hK (1 / 2) (by norm_num) hback
  have hfinite := first_regeneration_finite_of_hitting_and_return hd Q lam h0 h1 l δ hl hsep
    hδ0 hδ1 P K hK κ C hκ hhit (1 / 2) (by norm_num) (by norm_num) hreturn
  refine ⟨no_return_mass_of_quenched hd Q.measure P K hK.1 hK.2.1 (l / lam) _ ?_, ?_⟩
  · filter_upwards [hback] with ω hω
    exact hω 0
  · refine ⟨min (κ / 2) (s * κ / 2), C + D * Real.exp (12 * s * l),
      lt_min (by positivity) (by positivity), by positivity, ?_⟩
    intro t ht
    have hEnd := first_regeneration_endpoint_tail_of_exp_moment Q.measure K hK.1
      (Renewal.regenDelta lam) lam (l / lam) (Renewal.forceCoord hd) s D hs.le hint hmoment
    have hHit := annealed_forward_hitting_bound Q.measure P K hK.1 hK.2.1 lam κ C
      (Renewal.forceCoord hd) hhit
    have ht' := first_regeneration_tail_of_hitting_and_endpoint Q.measure K hK.1
      (Renewal.regenDelta lam) (EinsteinRelation.regenDelta_pos h0) lam l h0 hl
      (Renewal.forceCoord hd) hK.2.2.2.2.2.1 hfinite κ s C D hκ.le hC hD hHit hEnd t.toNNReal
    simpa only [regenerationTime, Regeneration.regenerationTime_one,
      ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ ht] using ht'

end EinsteinFull.Regeneration
