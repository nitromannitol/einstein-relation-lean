import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_condition_u2D_iterate
import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_independence
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.Regeneration.C1ConditionIterateSupport
import EinsteinRelation.Regeneration.KilledFutureConditionalMean

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

/-- The first conjunct of the condition-iterate node: the original barrier
on a selected slice is precisely survival before the successful bridge. -/
theorem c1_prebridge_survival {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (n : ℕ) (hn : 2 ≤ n) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) →
      (q ∈ regenerationNoReturn hd (l / lam) ↔
        ∀ s : ℝ≥0, s ≤ (n - 1 : ℕ) * Renewal.regenDelta lam →
          -(l / lam) < q.2.1 s (Renewal.forceCoord hd)) := by
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hbar := ae_noBacktracking_iff_prefix_on_firstRegenerationSlice Q.measure K hK.1
    (Renewal.regenDelta lam) hΔ lam (l / lam) h₀ (div_pos hl h₀)
    (Renewal.forceCoord hd) (n - 1) hK.2.2.2.2.2.1
  have hstart := ae_origin_start_of_isGMPReducedKernel hd Q lam h₀.le h₁ P K
    hK.1 hK.2.1 hK.2.2.1
  filter_upwards [hbar, hstart] with q hq hq0
  intro ht
  have htime : firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) =
      ((((n - 1 + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) := by
    simpa only [EinsteinFull.regenerationTime, regenerationTime_one,
      Nat.sub_add_cancel (by omega : 1 ≤ n)] using ht
  have hb := hq htime
  simpa only [regenerationNoReturn, Set.mem_setOf_eq, hq0, Pi.zero_apply, sub_zero]
    using hb

/-- Inserting prebridge survival into the exact finite-history test gives
factorization on every deterministic slice under the D-conditioned law. -/
theorem c1_conditioned_slice_factor
    (hindep : node_app_u3A_factorization_u23_independenceStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n)
    (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂ν) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 ∂ν) * ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν := by
  classical
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  let μ := annealedCoupledLaw Q.measure K
  let S : Set (FieldPair d × CoupledSample d) :=
    {q | regenerationTime hd lam l 1 q.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  let E : Set (CoupledSample d) :=
    {z | ∀ t : ℝ≥0, t ≤ (n - 1 : ℕ) * Δ → -R < z.1 t i - z.1 0 i}
  have hEm : MeasurableSet[finiteHistorySigma Δ (n - 1)] E :=
    measurableSet_noBacktracking_prefix Δ (n - 1) R i
  have hsm : MeasurableSet S := measurableSet_eq_fun
    ((measurable_regenerationTime Δ lam R i 1).comp measurable_snd) measurable_const
  have hdm : MeasurableSet (regenerationNoReturn hd R) :=
    (measurableSet_NoBacktracking R i).preimage measurable_snd.fst
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hbar := ae_noBacktracking_iff_prefix_on_firstRegenerationSlice Q.measure K hK.1
    Δ hΔ lam R h₀ (div_pos hl h₀) i (n - 1) hK.2.2.2.2.2.1
  have hDE : ∀ᵐ q ∂μ.restrict S, q ∈ regenerationNoReturn hd R ↔ q.2 ∈ E := by
    filter_upwards [ae_restrict_of_ae hbar, ae_restrict_mem hsm] with q hq ht
    apply hq
    simpa only [S, Set.mem_setOf_eq, EinsteinFull.regenerationTime,
      regenerationTime_one, Nat.sub_add_cancel (by omega : 1 ≤ n)] using ht
  have hbEH : BoundedRealTest (E.indicator H) := by
    obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ E
    · simpa only [Set.indicator_of_mem hz] using (hC z).trans (le_max_left C 0)
    · simpa only [Set.indicator_of_notMem hz, abs_zero] using le_max_right C 0
  have hfactor := ((hindep d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    Φ hΦ hbΦ).1 F hF hbF n hn (E.indicator H) (hH.indicator hEm) hbEH).2.2.2.2
  dsimp only
  apply EinsteinFull.Regeneration.conditional_slice_of_indicator μ
    (regenerationNoReturn hd R) S (Prod.snd ⁻¹' E) hdm hsm hDE
  have heq (q : FieldPair d × CoupledSample d) :
      (Prod.snd ⁻¹' E).indicator (fun q => F q.1 * H q.2 *
        Φ (regenerationRecord hd lam l 1 q)) q =
      F q.1 * E.indicator H q.2 * Φ (regenerationRecord hd lam l 1 q) := by
    by_cases hq : q.2 ∈ E <;> simp [hq]
  have heq' (q : FieldPair d × CoupledSample d) :
      (Prod.snd ⁻¹' E).indicator (fun q => F q.1 * H q.2) q =
      F q.1 * E.indicator H q.2 := by
    by_cases hq : q.2 ∈ E <;> simp [hq]
  simp only [heq, heq']
  exact hfactor

end EinsteinFull.Blueprint
