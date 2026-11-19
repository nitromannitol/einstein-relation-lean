import EinsteinFull.Regeneration.GuardEstimate
import EinsteinFull.Regeneration.PassagesFromHitting

/-!
# Finiteness of the first regeneration time

Forward-hitting estimates and conditional no-return estimates imply that the
literal trial construction reaches a finite first regeneration time.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration EinsteinFull.Blueprint
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The first regeneration is finite when forward hitting and conditional
no-return hold for the supplied coupling. -/
theorem first_regeneration_finite_of_hitting_and_return {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (κ C : ℝ) (hκ : 0 < κ)
    (hhit : ∀ (T : ℝ≥0) (a : ℝ), ∀ᵐ ω ∂Q.measure,
      P (0, ω) {γ | (T : ℝ≥0∞) ≤ firstHittingAbove γ (Renewal.forceCoord hd) a} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam ^ 2 * T + lam * a)))
    (η : ℝ) (hη : 0 < η) (hη1 : η ≤ 1)
    (hreturn : ∀ n : ℕ,
      let μ := annealedCoupledLaw Q.measure K
      let Δ := Renewal.regenDelta lam
      let R := l / lam
      let i := Renewal.forceCoord hd
      let E := {q : FieldPair d × CoupledSample d | trialStartSequence Δ lam R q.2 i n ≠ ⊤}
      η * μ.real E ≤ μ.real (E ∩ {q | NoBacktracking R
        (pathTimeShift q.2.1 (trialStartSequence Δ lam R q.2 i n).toNNReal) i})) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤ := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  obtain ⟨ε, hε, hε1, hguard⟩ := guard_estimate hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
  have hhit' := annealed_forward_hitting_bound Q.measure P K hK.1 hK.2.1 lam κ C
    (Renewal.forceCoord hd) hhit
  have hpass := ae_shifted_passages_finite_of_forward_hitting_bound
    (annealedCoupledLaw Q.measure K) (Renewal.forceCoord hd) lam κ C h0 hκ hhit'
  apply coupling_scope_ae_first_regeneration_finite_of_guard_and_return_estimates
    Q.measure K hK.1 (Renewal.regenDelta lam) (EinsteinRelation.regenDelta_pos h0)
    δ hδ0 hδ1.le hK.2.2.2.1 lam (l / lam) h0 (div_pos hl h0) (Renewal.forceCoord hd)
    ε hε hε1 _ hguard η hη hη1 hreturn
  intro m A _hA
  filter_upwards [hpass] with q hq n
  exact hq (Renewal.regenDelta lam) (l / lam) ((m : ℝ≥0) * Renewal.regenDelta lam) (A q.2) n

end EinsteinFull.Regeneration
