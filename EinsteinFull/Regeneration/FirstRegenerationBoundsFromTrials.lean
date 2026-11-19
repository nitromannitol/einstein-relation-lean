import EinsteinFull.Regeneration.FirstRegenerationBoundsFromHitting
import EinsteinFull.Regeneration.TrialEndpointMoment

/-!
# Regeneration bounds from weighted trial moments

The geometric trial-moment estimate in Shen's proof supplies the endpoint
moment used to obtain the first-regeneration tail.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Uniform hitting estimates and geometric weighted trial moments imply the
no-return and first-regeneration tail conclusions. -/
theorem first_regeneration_bounds_of_trial_moments {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (κ a C B q : ℝ) (hκ : 0 < κ) (ha : 0 < a) (hC : 0 < C)
    (hB : 0 < B) (hq : 0 ≤ q) (hq1 : q < 1)
    (hback : ∀ᵐ ω ∂Q.measure, ∀ x, ENNReal.ofReal (1 / 2 : ℝ) ≤
      P (x, ω) {γ | NoBacktracking (l / lam) γ (Renewal.forceCoord hd)})
    (hhit : ∀ (T : ℝ≥0) (v : ℝ), 0 ≤ v → ∀ᵐ ω ∂Q.measure,
      P (0, ω) {γ | (T : ℝ≥0∞) ≤ firstHittingAbove γ (Renewal.forceCoord hd) v} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam ^ 2 * T + lam * v)))
    (htrial : ∀ n : ℕ,
      let Δ := Renewal.regenDelta lam
      let R := l / lam
      let i := Renewal.forceCoord hd
      let E := {z : FieldPair d × CoupledSample d | trialStartSequence Δ lam R z.2 i n ≠ ⊤}
      let F := fun z : FieldPair d × CoupledSample d => ENNReal.ofReal (Real.exp (a *
        (lam * (z.2.1 (trialStartSequence Δ lam R z.2 i n).toNNReal i - z.2.1 0 i))))
      (∫⁻ z, E.indicator F z ∂annealedCoupledLaw Q.measure K) ≤ ENNReal.ofReal (B * q ^ n)) :
    ENNReal.ofReal (1 / 2 : ℝ) ≤ annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ∧
    ∃ c C' : ℝ, 0 < c ∧ 0 < C' ∧ ∀ t : ℝ, 0 ≤ t →
      annealedCoupledLaw Q.measure K {z | ENNReal.ofReal t < regenerationTime hd lam l 1 z.2} ≤
        ENNReal.ofReal (C' * Real.exp (-c * lam ^ 2 * t)) := by
  have hreturn := trial_return_estimate_of_uniform_no_backtracking hd Q lam h0 h1 l δ hl
    P K hK (1 / 2) (by norm_num) hback
  have hfinite := first_regeneration_finite_of_hitting_and_return hd Q lam h0 h1 l δ hl hsep
    hδ0 hδ1 P K hK κ C hκ hhit (1 / 2) (by norm_num) (by norm_num) hreturn
  obtain ⟨hm, hmoment⟩ := first_regeneration_endpoint_moment_of_trial_bounds
    (annealedCoupledLaw Q.measure K) (Renewal.regenDelta lam) (EinsteinRelation.regenDelta_pos h0)
    lam (l / lam) a (Renewal.forceCoord hd) B q hB.le hq hq1 hfinite htrial
  exact first_regeneration_bounds_of_hitting_and_moment hd Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK κ a C (B / (1 - q)) hκ ha hC (div_pos hB (sub_pos.mpr hq1)) hback hhit hm hmoment

end EinsteinFull.Regeneration
