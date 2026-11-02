import EinsteinRelation.Regeneration.FiniteHistoryTrialEvent
import EinsteinRelation.Regeneration.ForcedBitGeometry
import EinsteinRelation.Regeneration.HalfSpaces

/-! # The no-backtracking event on a regeneration slice

Source `paper/main.tex:412–425`. On a first-regeneration slice, the successful
bridge remains above the original barrier, and the nonbacktracking future does
so as well. Thus the original no-backtracking event is the event that the path
before the final interval avoids the barrier. That event belongs to the exact
finite-history sigma-algebra needed for conditional invariance.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

/-- Avoiding the downward hitting level is equivalent to staying strictly
above it at every finite time (`paper/main.tex:279–281,412–425`). -/
theorem noBacktracking_iff_forall {d : ℕ} (R : ℝ) (γ : Path d) (i : Fin d) :
    NoBacktracking R γ i ↔ ∀ t : ℝ≥0, -R < γ t i - γ 0 i := by
  constructor
  · intro h t
    by_contra ht
    have hhit := firstHittingBelow_le_of_crossing γ i (-R) t (le_of_not_gt ht)
    rw [show firstHittingBelow γ i (-R) = ⊤ from h] at hhit
    exact (not_le_of_gt ENNReal.coe_lt_top) hhit
  · intro h
    change (⨅ (t : ℝ≥0) (_ : γ t i - γ 0 i ≤ -R), (t : ℝ≥0∞)) = ⊤
    apply top_unique
    refine le_iInf fun t => le_iInf fun ht => ?_
    exact False.elim ((not_le_of_gt (h t)) ht)

/-- Barrier avoidance through `mΔ` is measurable in the literal finite history
(`paper/main.tex:412–425`). -/
theorem measurableSet_noBacktracking_prefix {d : ℕ} (Δ : ℝ≥0) (m : ℕ)
    (R : ℝ) (i : Fin d) :
    @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ m)
      {z | ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i} := by
  have hset : {z : CoupledSample d |
      ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i} =
      Probability.stoppedHistorySample Δ m ⁻¹' {z | NoBacktracking R z.1 i} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq, noBacktracking_iff_forall]
    constructor
    · intro h t
      change -R < z.1 (min t ((m : ℝ≥0) * Δ)) i -
        z.1 (min 0 ((m : ℝ≥0) * Δ)) i
      rw [min_eq_left zero_le]
      exact h _ (min_le_right _ _)
    · intro h t ht
      have hs := h t
      rw [Probability.stoppedHistorySample_path Δ m z t ht,
        Probability.stoppedHistorySample_path Δ m z 0 zero_le] at hs
      exact hs
  rw [hset]
  exact Probability.measurable_stoppedHistorySample Δ m
    ((measurableSet_NoBacktracking R i).preimage measurable_fst)

private theorem bridge_height {d : ℕ} (R : ℝ) (i : Fin d) (x y : Vec d)
    (hy : y ∈ couplingRegion i R x) : x i - R < y i := by
  have hnorm := coordinate_abs_le_euclideanNorm (y - (x + (5 * R) • unitVector i)) i
  have hlow := (abs_lt.mp (hnorm.trans_lt hy)).1
  have heq : (y - (x + (5 * R) • unitVector i)) i = y i - (x i + 5 * R) := by
    simp [unitVector]
  linarith

/-- On a first-regeneration slice with its actual successful bridge support,
no-backtracking is precisely avoidance of the original barrier before the last
interval (`paper/main.tex:412–425`). -/
theorem noBacktracking_iff_prefix_on_firstRegenerationSlice {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (z : CoupledSample d) (i : Fin d) (m : ℕ)
    (hτ : firstRegenerationTime Δ lam R z i =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞))
    (hbridge : ∀ t : ℝ≥0, (m : ℝ≥0) * Δ ≤ t →
      t ≤ ((m + 1 : ℕ) : ℝ≥0) * Δ →
      z.1 t ∈ couplingRegion i R (z.1 ((m : ℝ≥0) * Δ))) :
    NoBacktracking R z.1 i ↔
      ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i := by
  obtain ⟨hΓ, _, hfuture⟩ :=
    (firstRegenerationTime_eq_iff_forcedBitTrialEvent Δ hΔ lam R z i m).mp hτ
  have hheight := (forcedBitTrialEvent_geometry Δ hΔ lam R hlam hR i m z hΓ).2
  have hMN : (m : ℝ≥0) * Δ ≤ ((m + 1 : ℕ) : ℝ≥0) * Δ := by
    exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.le_succ m) zero_le
  have hlast : ∀ t : ℝ≥0, (m : ℝ≥0) * Δ ≤ t →
      t ≤ ((m + 1 : ℕ) : ℝ≥0) * Δ → R < z.1 t i - z.1 0 i := by
    intro t ht ht'
    have hlow := bridge_height R i _ _ (hbridge t ht ht')
    linarith
  rw [noBacktracking_iff_forall] at hfuture ⊢
  constructor
  · exact fun h t _ => h t
  · intro hpast t
    by_cases ht : t ≤ (m : ℝ≥0) * Δ
    · exact hpast t ht
    · by_cases ht' : t ≤ ((m + 1 : ℕ) : ℝ≥0) * Δ
      · have hlow := hlast t (le_of_not_ge ht) ht'
        linarith
      · have hN : ((m + 1 : ℕ) : ℝ≥0) * Δ ≤ t := le_of_not_ge ht'
        have hf := hfuture (t - ((m + 1 : ℕ) : ℝ≥0) * Δ)
        change -R < z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ +
          (t - ((m + 1 : ℕ) : ℝ≥0) * Δ)) i -
          z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ + 0) i at hf
        rw [add_tsub_cancel_of_le hN, add_zero] at hf
        have hend := hlast (((m + 1 : ℕ) : ℝ≥0) * Δ) hMN le_rfl
        linarith

/-- The preceding barrier identity holds under the actual annealed coupled law,
using only the origin-a.e. successful-bridge support from the frozen coupling
(`paper/main.tex:412–425`). -/
theorem ae_noBacktracking_iff_prefix_on_firstRegenerationSlice {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (m : ℕ) (hsupport : HasSuccessfulBridgeSupport Q Δ i R K) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      firstRegenerationTime Δ lam R ωz.2 i =
          ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) →
        (NoBacktracking R ωz.2.1 i ↔
          ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → -R < ωz.2.1 t i - ωz.2.1 0 i) := by
  have htime : MeasurableSet {ωz : FieldPair d × CoupledSample d |
      firstRegenerationTime Δ lam R ωz.2 i =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} :=
    measurableSet_eq_fun
      ((measurable_firstRegenerationTime Δ lam R i).comp measurable_snd) measurable_const
  have hD : MeasurableSet {ωz : FieldPair d × CoupledSample d |
      NoBacktracking R ωz.2.1 i} :=
    (measurableSet_NoBacktracking R i).preimage measurable_snd.fst
  have hpast := (Probability.finiteHistorySigma_le (d := d) Δ m) _
    (measurableSet_noBacktracking_prefix Δ m R i)
  have hPast : MeasurableSet {ωz : FieldPair d × CoupledSample d |
      ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → -R < ωz.2.1 t i - ωz.2.1 0 i} :=
    hpast.preimage measurable_snd
  apply Measure.ae_compProd_of_ae_ae (htime.imp (hD.iff hPast))
  filter_upwards [hK.1, hsupport.1] with ω hprob hsupp
  haveI : IsProbabilityMeasure (originCoupledLaw K ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  filter_upwards [hsupp] with z hz
  intro hτ
  have hb := firstRegenerationTime_last_bit Δ hΔ lam R z i m hτ
  exact noBacktracking_iff_prefix_on_firstRegenerationSlice Δ hΔ lam R hlam hR z i m hτ
    (hz m hb)


end EinsteinRelation.Regeneration
