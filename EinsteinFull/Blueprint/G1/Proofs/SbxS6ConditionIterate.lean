import EinsteinFull.Blueprint.G1.Proofs.C1ConditionIterate
import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.Work.W1.RegenerationReuseSupport
import EinsteinRelation.Regeneration.FirstSlicePastLocality
import EinsteinRelation.Regeneration.RecenterNoBacktracking

/-!
# All-scale support for the condition-iterate reduction

These adapters use the exact independence V2 hypothesis and preserve the
original construction scale. They establish finite-slice clauses and the
supplied annealed first marginal. Summing the centered residual also proves
conditional first-record invariance without assuming first-time finiteness.
An infinity-event alternative also gives every conditioned record marginal
and one invariant measurable shift composing all the conditioned records.
Annealed later-cycle composition remains a separate obligation.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

/-- Inserting prebridge survival into the exact finite-history test gives
factorization on every deterministic slice under the D-conditioned law. -/
theorem sbx_s6_conditioned_slice_factor_v2
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
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
    ((Regeneration.measurable_regenerationTime Δ lam R i 1).comp measurable_snd) measurable_const
  have hdm : MeasurableSet (regenerationNoReturn hd R) :=
    (measurableSet_NoBacktracking R i).preimage measurable_snd.fst
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hbar := ae_noBacktracking_iff_prefix_on_firstRegenerationSlice Q.measure K hK.1
    Δ hΔ lam R h₀ (div_pos hl h₀) i (n - 1) hK.2.2.2.2.2.1
  have hDE : ∀ᵐ q ∂μ.restrict S, q ∈ regenerationNoReturn hd R ↔ q.2 ∈ E := by
    filter_upwards [ae_restrict_of_ae hbar, ae_restrict_mem hsm] with q hq ht
    apply hq
    simpa only [S, Set.mem_ofPred_eq, EinsteinFull.regenerationTime,
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


/-- The literal infinity fallback returns the zero-time record. -/
theorem sbx_s6_record_first_eq_zero_of_infinite
    {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (q : FieldPair d × CoupledSample d)
    (h : firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) = ⊤) :
    regenerationRecord hd lam l 1 q = regenerationRecord hd lam l 0 q := by
  change futureRecord _ _ _ _ _ (Regeneration.regenerationTime _ _ _ _ _ 1).toNNReal =
    futureRecord _ _ _ _ _ (Regeneration.regenerationTime _ _ _ _ _ 0).toNNReal
  rw [Regeneration.regenerationTime_one, h]
  rfl

/-- Once the first time is infinite, every literal record uses time zero. -/
theorem sbx_s6_all_records_eq_zero_of_infinite
    {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (q : FieldPair d × CoupledSample d)
    (h : firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) = ⊤) (k : ℕ) :
    regenerationRecord hd lam l k q = regenerationRecord hd lam l 0 q := by
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have htop : ∀ j, Regeneration.regenerationTime Δ lam R q.2 i (j + 1) = ⊤ := by
    intro j
    induction j with
    | zero => exact (Regeneration.regenerationTime_one Δ lam R q.2 i).trans h
    | succ j hj => rw [Regeneration.regenerationTime, hj, ite_eq_left rfl]
  cases k with
  | zero => rfl
  | succ j =>
      change futureRecord Δ R q.1 q.2 i
        (Regeneration.regenerationTime Δ lam R q.2 i (j + 1)).toNNReal =
          futureRecord Δ R q.1 q.2 i 0
      rw [htop j]
      rfl

/-- The zero record retains the first regeneration time through its sample. -/
theorem sbx_s6_zero_record_first_time
    {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (q : FieldPair d × CoupledSample d) :
    firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam)
      (recordSample (regenerationRecord hd lam l 0 q)) (Renewal.forceCoord hd) =
        firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
          (Renewal.forceCoord hd) := by
  change firstRegenerationTime _ _ _
    (recordSample (futureRecord _ _ q.1 q.2 _ 0)) _ = _
  change firstRegenerationTime _ _ _
    (recenterSample (q.2.1 0) (sampleTimeShift _ q.2 0)) _ = _
  rw [firstRegenerationTime_recenterSample, sampleTimeShift_zero]

/-- The record at zero preserves the relative no-return event. -/
theorem sbx_s6_zero_record_no_return_iff
    {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ) (q : FieldPair d × CoupledSample d) :
    NoBacktracking (l / lam) (regenerationRecord hd lam l 0 q).1
      (Renewal.forceCoord hd) ↔ q ∈ regenerationNoReturn hd (l / lam) := by
  have hpath : (regenerationRecord hd lam l 0 q).1 =
      (recenterSample (q.2.1 0) q.2).1 := by
    ext t j
    change (q.2.1 (0 + t) - q.2.1 0) j = (q.2.1 t - q.2.1 0) j
    rw [zero_add]
  rw [hpath]
  exact noBacktracking_recenterSample_iff _ _ _ _

/-- Summing zero integrals on the actual finite slices leaves precisely the
infinity residual. No full-measure cover or finiteness assumption is used. -/
theorem sbx_s6_integral_eq_infinity_of_slice_zero
    {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (ρ : Measure (FieldPair d × CoupledSample d))
    (f : FieldPair d × CoupledSample d → ℝ) (hf : Integrable f ρ)
    (hslice : ∀ m : ℕ, (∫ q in {q | firstRegenerationTime Δ lam R q.2 i =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, f q ∂ρ) = 0) :
    (∫ q, f q ∂ρ) = ∫ q in {q | firstRegenerationTime Δ lam R q.2 i = ⊤}, f q ∂ρ := by
  let S : ℕ → Set (FieldPair d × CoupledSample d) := fun m =>
    {q | firstRegenerationTime Δ lam R q.2 i =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  let E : Set (FieldPair d × CoupledSample d) :=
    {q | firstRegenerationTime Δ lam R q.2 i = ⊤}
  have hEm : MeasurableSet E := measurableSet_eq_fun
    ((measurable_firstRegenerationTime Δ lam R i).comp measurable_snd) measurable_const
  have hSm : ∀ m, MeasurableSet (S m) := fun _ => measurableSet_eq_fun
    ((measurable_firstRegenerationTime Δ lam R i).comp measurable_snd) measurable_const
  have hcover : (⋃ m, S m) = Eᶜ := by
    ext q
    constructor
    · intro hq
      obtain ⟨m, hm⟩ := Set.mem_iUnion.mp hq
      exact fun htop => ENNReal.coe_ne_top (hm.symm.trans htop)
    · intro hq
      obtain ⟨m, hm⟩ := firstRegenerationTime_eq_succ_grid_of_ne_top Δ hΔ lam R q.2 i hq
      exact Set.mem_iUnion.mpr ⟨m, hm⟩
  have hsum := hasSum_integral_iUnion hSm
    (pairwise_disjoint_firstRegenerationSlices Δ hΔ lam R i) hf.integrableOn
  have hzero : (∫ q in Eᶜ, f q ∂ρ) = 0 := by
    rw [← hcover]
    apply hsum.unique
    simpa only [S, hslice] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℝ)) 0)
  have hsplit := integral_add_compl hEm hf
  rw [hzero, add_zero] at hsplit
  exact hsplit.symm

section AllScale

variable (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
  {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
  (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
  (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ : 0 < δ) (hδ₁ : δ < 1)
  (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
  (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
  (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)

include hindep h₀ h₁ hl hsep hδ hδ₁ hK hD

/-- The deterministic-slice target clause holds under both source laws at
 every positive separated construction scale. No tail bound is used. -/
theorem sbx_s6_slice_factor_both
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ)
    (F : FieldPair d → ℝ)
    (hF : Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F)
    (hbF : BoundedRealTest F) (n : ℕ) (hn : 2 ≤ n)
    (H : CoupledSample d → ℝ)
    (hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (n - 1)] H)
    (hbH : BoundedRealTest H) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
    (∫ q in {q | regenerationTime hd lam l 1 q.2 =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * H q.2 ∂ρ) *
      ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  dsimp only
  intro ρ hρ
  rcases Set.mem_insert_iff.mp hρ with rfl | hρ
  · exact ((hindep d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
      Φ hΦ hbΦ).1 F hF hbF n hn H hH hbH).2.2.2.2
  · obtain rfl := Set.mem_singleton_iff.mp hρ
    exact sbx_s6_conditioned_slice_factor_v2 hindep hd Q lam h₀ h₁ l δ hl hsep
      hδ hδ₁ P K hK hD Φ hΦ hbΦ F hF hbF n hn H hH hbH

/-- The annealed first-record marginal is an exact conjunct of independence V2,
 available at the original admissible scale. -/
theorem sbx_s6_annealed_first_marginal
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q, Φ (regenerationRecord hd lam l 1 q) ∂annealedCoupledLaw Q.measure K) =
      ∫ q, Φ (regenerationRecord hd lam l 0 q)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD :=
  (hindep d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD Φ hΦ hbΦ).2

/-- Independence V2 supplies the library's complete positive-grid slice
interface. The omitted index zero is empty by the literal trial geometry. -/
theorem sbx_s6_first_regeneration_slice_factor :
    FirstRegenerationSliceFactor Q.measure K (Renewal.regenDelta lam)
      lam (l / lam) (Renewal.forceCoord hd) := by
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  intro Φ hΦ hbΦ m H hH hbH
  by_cases hm : m = 0
  · subst m
    have hempty : {q : FieldPair d × CoupledSample d |
        firstRegenerationTime Δ lam R q.2 i =
          ((((0 + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have htrial := ((firstRegenerationTime_eq_iff_forcedBitTrialEvent
        Δ hΔ lam R q.2 i 0).mp hq).1
      rw [forcedBitTrialEvent_zero_eq_empty Δ hΔ lam R h₀ (div_pos hl h₀) i] at htrial
      exact htrial
    change (∫ q in {q : FieldPair d × CoupledSample d |
        firstRegenerationTime Δ lam R q.2 i =
          ((((0 + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
        H q.2 * Φ (iteratedRecord Δ lam R i 1 q) ∂annealedCoupledLaw Q.measure K) = _
    dsimp only [Δ, R, i] at hempty ⊢
    simp only [hempty, setIntegral_empty, mul_zero]
  · have hfactor := ((hindep d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
      Φ hΦ hbΦ).1 (fun _ => 1) measurable_const ⟨1, fun _ => by norm_num⟩
      (m + 1) (by omega) H (by simpa only [Nat.add_sub_cancel] using hH) hbH).2.2.2.2
    simpa only [one_mul, Nat.add_sub_cancel, EinsteinFull.regenerationTime,
      regenerationTime_one, EinsteinFull.regenerationRecord_eq_iteratedRecord,
      EinsteinFull.regenerationConditionedLaw_eq_cond] using hfactor.trans (mul_comm _ _)

/-- The full supplied annealed marginal as an equality of actual record laws. -/
theorem sbx_s6_annealed_first_law :
    (annealedCoupledLaw Q.measure K).map (regenerationRecord hd lam l 1) =
      (regenerationConditionedLaw hd Q lam l K hK.1 hD).map
        (regenerationRecord hd lam l 0) := by
  have := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  apply measure_eq_of_bounded_real_tests
  intro Φ hΦ hbΦ
  rw [integral_map (EinsteinFull.measurable_regenerationRecord hd lam l 1).aemeasurable
      hΦ.aestronglyMeasurable,
    integral_map (EinsteinFull.measurable_regenerationRecord hd lam l 0).aemeasurable
      hΦ.aestronglyMeasurable]
  exact sbx_s6_annealed_first_marginal hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    Φ hΦ hbΦ

/-- The full marginal and the infinity fallback put the infinite-time event
inside the original no-return event, almost everywhere. -/
theorem sbx_s6_infinity_implies_no_return :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) = ⊤ → q ∈ regenerationNoReturn hd (l / lam) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let B : Set (FutureState d (Renewal.forceCoord hd) (l / lam)) :=
    {y | NoBacktracking (l / lam) y.1 (Renewal.forceCoord hd)}
  have hBm : MeasurableSet B :=
    (measurableSet_NoBacktracking _ _).preimage measurable_fst
  have hν : ∀ᵐ q ∂ν, regenerationRecord hd lam l 0 q ∈ B := by
    have hmem : ∀ᵐ q ∂ν, q ∈ regenerationNoReturn hd (l / lam) :=
      ProbabilityTheory.ae_cond_mem (EinsteinFull.measurableSet_regenerationNoReturn hd _)
    filter_upwards [hmem] with q hq
    exact (sbx_s6_zero_record_no_return_iff hd lam l q).mpr hq
  have hmap : ∀ᵐ y ∂ν.map (regenerationRecord hd lam l 0), y ∈ B :=
    (ae_map_iff (EinsteinFull.measurable_regenerationRecord hd lam l 0).aemeasurable hBm).mpr hν
  rw [← sbx_s6_annealed_first_law hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD] at hmap
  have hμ := ae_of_ae_map
    (EinsteinFull.measurable_regenerationRecord hd lam l 1).aemeasurable hmap
  filter_upwards [hμ] with q hq htop
  rw [sbx_s6_record_first_eq_zero_of_infinite hd lam l q htop] at hq
  exact (sbx_s6_zero_record_no_return_iff hd lam l q).mp hq

/-- Both source laws have precisely the infinity residual for a centered
bounded first-record test; all finite slices cancel at the original scale. -/
theorem sbx_s6_centered_residual_both
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let a := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
    ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      (∫ q, (Φ (regenerationRecord hd lam l 1 q) - a) ∂ρ) =
        ∫ q in {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam)
          q.2 (Renewal.forceCoord hd) = ⊤},
          (Φ (regenerationRecord hd lam l 1 q) - a) ∂ρ := by
  dsimp only
  intro ρ hρ
  have := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have : IsProbabilityMeasure ρ := by
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · infer_instance
    · obtain rfl := Set.mem_singleton_iff.mp hρ
      infer_instance
  let a := ∫ q, Φ (regenerationRecord hd lam l 0 q)
    ∂regenerationConditionedLaw hd Q lam l K hK.1 hD
  have hf : Integrable (fun q => Φ (regenerationRecord hd lam l 1 q)) ρ := by
    obtain ⟨C, hC⟩ := hbΦ
    apply Integrable.of_bound
      (hΦ.comp (EinsteinFull.measurable_regenerationRecord hd lam l 1)).aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun q => by
      rw [Real.norm_eq_abs]
      exact hC _
  have hΔ : 0 < Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  apply sbx_s6_integral_eq_infinity_of_slice_zero _ hΔ _ _ _ ρ _ (hf.sub (integrable_const a))
  intro m
  by_cases hm : m = 0
  · subst m
    have hempty : {q : FieldPair d × CoupledSample d |
        firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2 (Renewal.forceCoord hd) =
          ((((0 + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro q hq
      have ht := ((firstRegenerationTime_eq_iff_forcedBitTrialEvent _ hΔ _ _ _ _ 0).mp hq).1
      rw [forcedBitTrialEvent_zero_eq_empty _ hΔ _ _ h₀ (div_pos hl h₀) _] at ht
      exact ht
    rw [hempty, setIntegral_empty]
  · have hfactor := sbx_s6_slice_factor_both hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
      Φ hΦ hbΦ (fun _ => 1) measurable_const ⟨1, fun _ => by norm_num⟩
      (m + 1) (by omega) (fun _ => 1) measurable_const ⟨1, fun _ => by norm_num⟩ ρ hρ
    simp only [one_mul, EinsteinFull.regenerationTime, regenerationTime_one] at hfactor
    simp only [Pi.sub_apply]
    rw [integral_sub hf.integrableOn (integrable_const a), hfactor]
    simp only [integral_const, smul_eq_mul, measureReal_def, mul_one, a, sub_self]

/-- Conditional first-record invariance from the centered infinity residual,
without any first-time finiteness assumption. -/
theorem sbx_s6_conditional_first_integral
    (Φ : FutureState d (Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q, Φ (regenerationRecord hd lam l 1 q)
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) =
    ∫ q, Φ (regenerationRecord hd lam l 0 q)
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let E : Set (FieldPair d × CoupledSample d) :=
    {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) = ⊤}
  let D := regenerationNoReturn hd (l / lam)
  let a := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
  let f := fun q => Φ (regenerationRecord hd lam l 1 q) - a
  have := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hf (ρ : Measure (FieldPair d × CoupledSample d)) [IsFiniteMeasure ρ] :
      Integrable (fun q => Φ (regenerationRecord hd lam l 1 q)) ρ := by
    obtain ⟨C, hC⟩ := hbΦ
    apply Integrable.of_bound
      (hΦ.comp (EinsteinFull.measurable_regenerationRecord hd lam l 1)).aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hC _
  have hcenter (ρ : Measure (FieldPair d × CoupledSample d)) [IsProbabilityMeasure ρ] :
      (∫ q, f q ∂ρ) = (∫ q, Φ (regenerationRecord hd lam l 1 q) ∂ρ) - a := by
    rw [integral_sub (hf ρ) (integrable_const a)]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  have hres := sbx_s6_centered_residual_both hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    Φ hΦ hbΦ
  have hzero : (∫ q in E, f q ∂μ) = 0 := by
    rw [← hres μ (by exact Or.inl rfl), hcenter μ,
      sbx_s6_annealed_first_marginal hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
        Φ hΦ hbΦ]
    exact sub_self a
  have hEm : MeasurableSet E := measurableSet_eq_fun
    ((measurable_firstRegenerationTime _ _ _ _).comp measurable_snd) measurable_const
  have hED : E ∩ D =ᵐ[μ] E := by
    filter_upwards [sbx_s6_infinity_implies_no_return hindep hd Q lam h₀ h₁ l δ hl hsep
      hδ hδ₁ P K hK hD] with q hq
    exact propext ⟨fun h => h.1, fun h => ⟨h, hq h⟩⟩
  have hrestrict : ν.restrict E = (μ D)⁻¹ • μ.restrict E := by
    change (ProbabilityTheory.cond μ D).restrict E = _
    rw [ProbabilityTheory.cond, Measure.restrict_smul, Measure.restrict_restrict hEm,
      Measure.restrict_congr_set hED]
  have hzeroν : (∫ q, f q ∂ν) = 0 := by
    rw [hres ν (by exact Or.inr rfl), hrestrict, integral_smul_measure, hzero, smul_zero]
  have heq := hcenter ν
  rw [hzeroν] at heq
  exact sub_eq_zero.mp heq.symm

/-- Equality of the conditioned first and zero record laws at all scales. -/
theorem sbx_s6_conditional_first_law :
    (regenerationConditionedLaw hd Q lam l K hK.1 hD).map (regenerationRecord hd lam l 1) =
      (regenerationConditionedLaw hd Q lam l K hK.1 hD).map (regenerationRecord hd lam l 0) := by
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  apply measure_eq_of_bounded_real_tests
  intro Φ hΦ hbΦ
  rw [integral_map (EinsteinFull.measurable_regenerationRecord hd lam l 1).aemeasurable
      hΦ.aestronglyMeasurable,
    integral_map (EinsteinFull.measurable_regenerationRecord hd lam l 0).aemeasurable
      hΦ.aestronglyMeasurable]
  exact sbx_s6_conditional_first_integral hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    Φ hΦ hbΦ

/-- The infinity residual has the full conditioned zero-record distribution,
scaled by its actual mass; the residual mass is not asserted to vanish. -/
theorem sbx_s6_infinity_record_law :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let E := {q : FieldPair d × CoupledSample d |
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) = ⊤}
    (μ.restrict E).map (regenerationRecord hd lam l 0) =
      (μ E) • ν.map (regenerationRecord hd lam l 0) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let E : Set (FieldPair d × CoupledSample d) :=
    {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) = ⊤}
  have := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have := Measure.smul_finite (ν.map (regenerationRecord hd lam l 0)) (measure_ne_top μ E)
  have hEm : MeasurableSet E := measurableSet_eq_fun
    ((measurable_firstRegenerationTime _ _ _ _).comp measurable_snd) measurable_const
  apply measure_eq_of_bounded_real_tests
  intro Φ hΦ hbΦ
  rw [integral_map (EinsteinFull.measurable_regenerationRecord hd lam l 0).aemeasurable
      hΦ.aestronglyMeasurable,
    integral_smul_measure,
    integral_map (EinsteinFull.measurable_regenerationRecord hd lam l 0).aemeasurable
      hΦ.aestronglyMeasurable]
  let a := ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν
  have hf : Integrable (fun q => Φ (regenerationRecord hd lam l 1 q)) μ := by
    obtain ⟨C, hC⟩ := hbΦ
    apply Integrable.of_bound
      (hΦ.comp (EinsteinFull.measurable_regenerationRecord hd lam l 1)).aestronglyMeasurable C
    exact Filter.Eventually.of_forall fun q => by rw [Real.norm_eq_abs]; exact hC _
  have hres := sbx_s6_centered_residual_both hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    Φ hΦ hbΦ
  have hzero : (∫ q in E, (Φ (regenerationRecord hd lam l 1 q) - a) ∂μ) = 0 := by
    rw [← hres μ (by exact Or.inl rfl), integral_sub hf (integrable_const a),
      sbx_s6_annealed_first_marginal hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
        Φ hΦ hbΦ]
    simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
    exact sub_self a
  have hrecords : (∫ q in E, Φ (regenerationRecord hd lam l 1 q) ∂μ) =
      ∫ q in E, Φ (regenerationRecord hd lam l 0 q) ∂μ := by
    apply setIntegral_congr_fun hEm
    intro q hq
    exact congrArg Φ (sbx_s6_record_first_eq_zero_of_infinite hd lam l q hq)
  rw [integral_sub hf.integrableOn (integrable_const a), hrecords] at hzero
  simpa only [integral_const, smul_eq_mul, measureReal_def,
    Measure.restrict_apply_univ, a] using sub_eq_zero.mp hzero

/-- The conditioned first time is either finite almost everywhere or infinite
almost everywhere. This alternative alone does not imply annealed finiteness. -/
theorem sbx_s6_conditioned_first_time_dichotomy :
    (∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤) ∨
    (∀ᵐ q ∂regenerationConditionedLaw hd Q lam l K hK.1 hD,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) = ⊤) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let E : Set (FieldPair d × CoupledSample d) :=
    {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) = ⊤}
  let A : Set (FutureState d (Renewal.forceCoord hd) (l / lam)) :=
    {y | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) (recordSample y)
      (Renewal.forceCoord hd) = ⊤}
  have := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hEm : MeasurableSet E := measurableSet_eq_fun
    ((measurable_firstRegenerationTime _ _ _ _).comp measurable_snd) measurable_const
  have hAm : MeasurableSet A := measurableSet_eq_fun
    ((measurable_firstRegenerationTime _ _ _ _).comp (measurable_recordSample _ _))
    measurable_const
  have hpre : (regenerationRecord hd lam l 0) ⁻¹' A = E := by
    ext q
    change (_ = ⊤) ↔ (_ = ⊤)
    rw [sbx_s6_zero_record_first_time hd lam l q]
  have hlaw := sbx_s6_infinity_record_law hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
  have hmass := congrArg (fun ρ : Measure (FutureState d (Renewal.forceCoord hd) (l / lam)) =>
    ρ A) hlaw
  rw [Measure.map_apply (EinsteinFull.measurable_regenerationRecord hd lam l 0) hAm,
    hpre, Measure.restrict_apply hEm, Set.inter_self, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (EinsteinFull.measurable_regenerationRecord hd lam l 0) hAm, hpre] at hmass
  by_cases hz : μ E = 0
  · exact Or.inl ((measure_eq_zero_iff_ae_notMem).mp hz)
  · right
    have hνE : ν E = 1 := (ENNReal.mul_eq_left hz (measure_ne_top μ E)).mp hmass.symm
    exact (mem_ae_iff_prob_eq_one hEm).mpr hνE

/-- Positive conditioned probability of a finite first time already forces
annealed almost-sure finiteness. This identifies the remaining original-scale
analytic input without assuming that the infinity residual vanishes. -/
theorem sbx_s6_first_finite_iff_conditioned_positive :
    (∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤) ↔
    (regenerationConditionedLaw hd Q lam l K hK.1 hD)
      {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
        (Renewal.forceCoord hd) ≠ ⊤} ≠ 0 := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let A : Set (FieldPair d × CoupledSample d) :=
    {q | firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
      (Renewal.forceCoord hd) ≠ ⊤}
  have hνμ : ν ≪ μ :=
    EinsteinFull.regenerationConditionedLaw_absolutelyContinuous hd Q lam l K hK.1 hD
  have := EinsteinFull.regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hAm : MeasurableSet A := (measurableSet_eq_fun
    ((measurable_firstRegenerationTime _ _ _ _).comp measurable_snd) measurable_const).compl
  constructor
  · intro hfin
    have hmass : ν A = 1 := (mem_ae_iff_prob_eq_one hAm).mp (hνμ.ae_le hfin)
    exact hmass.trans_ne one_ne_zero
  · intro hpos
    rcases sbx_s6_conditioned_first_time_dichotomy hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁
      P K hK hD with hfin | hinf
    · exact hfin
    · have hzero : ν A = 0 := (measure_eq_zero_iff_ae_notMem).mpr
        (hinf.mono fun _ hq hneq => hneq hq)
      exact (hpos hzero).elim

/-- Every actual record has the conditioned zero-record law, including the
infinite-time branch of the preceding alternative. -/
theorem sbx_s6_conditional_all_record_laws (k : ℕ) :
    (regenerationConditionedLaw hd Q lam l K hK.1 hD).map (regenerationRecord hd lam l k) =
      (regenerationConditionedLaw hd Q lam l K hK.1 hD).map (regenerationRecord hd lam l 0) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hνμ : ν ≪ μ :=
    EinsteinFull.regenerationConditionedLaw_absolutelyContinuous hd Q lam l K hK.1 hD
  rcases sbx_s6_conditioned_first_time_dichotomy hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁
    P K hK hD with hfin | hinf
  · have hfwd := ae_firstRegenerationTime_forward Q.measure K hK.1 Δ hΔ lam R h₀
      (div_pos hl h₀) i hK.2.2.2.2.2.1
    have hgood : ∀ᵐ q ∂ν, RecordCanShift Δ lam R i (iteratedRecord Δ lam R i 0 q) := by
      filter_upwards [hνμ.ae_le hfin, hνμ.ae_le hfwd] with q hq hforward
      change RecordCanShift Δ lam R i (futureRecord Δ R q.1 q.2 i 0)
      rw [recordCanShift_futureRecord_iff, sampleTimeShift_zero, zero_add]
      exact ⟨hq, hforward hq⟩
    have hcond := sbx_s6_conditional_first_law hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
    have hcond' : ν.map (iteratedRecord Δ lam R i 1) =
        ν.map (iteratedRecord Δ lam R i 0) := hcond
    cases k with
    | zero => rfl
    | succ j =>
        exact (iteratedRecord_law_of_first_and_conditional_law Δ hΔ lam R i ν ν
          Measure.AbsolutelyContinuous.rfl hgood hcond' hcond' j).2
  · apply Measure.map_congr
    filter_upwards [hinf] with q hq
    exact sbx_s6_all_records_eq_zero_of_infinite hd lam l q hq k

/-- One measurable invariant shift composes every actual conditioned record,
with the finite and infinite first-time branches treated separately. -/
theorem sbx_s6_conditioned_shift_all :
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    ∃ Θ : FutureState d (Renewal.forceCoord hd) (l / lam) →
        FutureState d (Renewal.forceCoord hd) (l / lam),
      Measurable Θ ∧
      (∀ k : ℕ, ∀ᵐ q ∂ν,
        Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      (ν.map (regenerationRecord hd lam l 0)).map Θ =
        ν.map (regenerationRecord hd lam l 0) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hνμ : ν ≪ μ :=
    EinsteinFull.regenerationConditionedLaw_absolutelyContinuous hd Q lam l K hK.1 hD
  obtain ⟨D, hDm, hdecode⟩ := Probability.exists_future_halfSpace_decoder i R
  let Θ := shiftRestrictedRecord Δ lam R i D
  have hΘ : Measurable Θ := measurable_shiftRestrictedRecord Δ lam R i D hDm
  have hfwd := ae_firstRegenerationTime_forward Q.measure K hK.1 Δ hΔ lam R h₀
    (div_pos hl h₀) i hK.2.2.2.2.2.1
  have hstep0 : ∀ᵐ q ∂ν,
      Θ (regenerationRecord hd lam l 0 q) = regenerationRecord hd lam l 1 q := by
    filter_upwards [hνμ.ae_le hfwd] with q hq
    have hforward : 0 ≤ q.2.1 (firstRegenerationTime Δ lam R q.2 i).toNNReal i -
        q.2.1 0 i := by
      by_cases hfin : firstRegenerationTime Δ lam R q.2 i = ⊤
      · simp only [hfin, ENNReal.toNNReal_top, sub_self, le_refl]
      · exact hq hfin
    have h := shiftRestrictedRecord_futureRecord Δ hΔ lam R i D hdecode q.1 q.2 0
      (by simpa only [Nat.cast_zero, zero_mul, zero_add, sampleTimeShift_zero] using hforward)
    change Θ (futureRecord Δ R q.1 q.2 i 0) =
      futureRecord Δ R q.1 q.2 i
        (Regeneration.regenerationTime Δ lam R q.2 i 1).toNNReal
    rw [Regeneration.regenerationTime_one]
    simpa only [Nat.cast_zero, zero_mul, zero_add, sampleTimeShift_zero] using h
  have hcond := sbx_s6_conditional_first_law hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
  refine ⟨Θ, hΘ, ?_, ?_⟩
  · rcases sbx_s6_conditioned_first_time_dichotomy hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁
      P K hK hD with hfin | hinf
    · have hgood : ∀ᵐ q ∂ν, RecordCanShift Δ lam R i (iteratedRecord Δ lam R i 0 q) := by
        filter_upwards [hνμ.ae_le hfin, hνμ.ae_le hfwd] with q hq hforward
        change RecordCanShift Δ lam R i (futureRecord Δ R q.1 q.2 i 0)
        rw [recordCanShift_futureRecord_iff, sampleTimeShift_zero, zero_add]
        exact ⟨hq, hforward hq⟩
      have hcond' : ν.map (iteratedRecord Δ lam R i 1) =
          ν.map (iteratedRecord Δ lam R i 0) := hcond
      have hiter := iteratedRecord_law_of_first_and_conditional_law Δ hΔ lam R i ν ν
        Measure.AbsolutelyContinuous.rfl hgood hcond' hcond'
      have hσgood : ∀ᵐ y ∂ν.map (iteratedRecord Δ lam R i 0), RecordCanShift Δ lam R i y :=
        (ae_map_iff (measurable_iteratedRecord Δ lam R i 0).aemeasurable
          (measurableSet_recordCanShift Δ lam R i)).mpr hgood
      intro k
      have hkgood : ∀ᵐ q ∂ν, RecordCanShift Δ lam R i (iteratedRecord Δ lam R i k q) := by
        have hmap : ν.map (iteratedRecord Δ lam R i k) =
            ν.map (iteratedRecord Δ lam R i 0) :=
          sbx_s6_conditional_all_record_laws hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD k
        rw [← hmap] at hσgood
        exact ae_of_ae_map (measurable_iteratedRecord Δ lam R i k).aemeasurable hσgood
      have hkfin : ∀ᵐ q ∂ν, Regeneration.regenerationTime Δ lam R q.2 i k ≠ ⊤ := by
        cases k with
        | zero =>
            exact Filter.Eventually.of_forall fun _ => by
              simp only [Regeneration.regenerationTime, ne_eq,
                ENNReal.zero_ne_top, not_false_eq_true]
        | succ j => exact (hiter j).1
      filter_upwards [hkgood, hkfin] with q hq hqfin
      exact (iteratedRecord_succ_of_canShift Δ hΔ lam R i D hdecode q k hqfin hq).2.symm
    · intro k
      filter_upwards [hinf, hstep0] with q hq hs
      calc
        Θ (regenerationRecord hd lam l k q) = Θ (regenerationRecord hd lam l 0 q) :=
          congrArg Θ (sbx_s6_all_records_eq_zero_of_infinite hd lam l q hq k)
        _ = regenerationRecord hd lam l 1 q := hs
        _ = regenerationRecord hd lam l 0 q :=
          sbx_s6_record_first_eq_zero_of_infinite hd lam l q hq
        _ = regenerationRecord hd lam l (k + 1) q :=
          (sbx_s6_all_records_eq_zero_of_infinite hd lam l q hq (k + 1)).symm
  · rw [Measure.map_map hΘ (EinsteinFull.measurable_regenerationRecord hd lam l 0)]
    exact (Measure.map_congr hstep0).trans hcond

/-- At the original scale, either all annealed record laws iterate correctly,
or every annealed record from index two onward uses the literal time-zero
fallback. The latter alternative is not a finiteness statement. -/
theorem sbx_s6_annealed_iteration_dichotomy :
    (∀ k : ℕ, 1 ≤ k →
      (annealedCoupledLaw Q.measure K).map (regenerationRecord hd lam l k) =
        (regenerationConditionedLaw hd Q lam l K hK.1 hD).map
          (regenerationRecord hd lam l 0)) ∨
    (∀ k : ℕ, 2 ≤ k → ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      regenerationRecord hd lam l k q = regenerationRecord hd lam l 0 q) := by
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hνμ : ν ≪ μ :=
    EinsteinFull.regenerationConditionedLaw_absolutelyContinuous hd Q lam l K hK.1 hD
  have hfirst : μ.map (iteratedRecord Δ lam R i 1) = ν.map (iteratedRecord Δ lam R i 0) :=
    sbx_s6_annealed_first_law hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
  rcases sbx_s6_conditioned_first_time_dichotomy hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁
    P K hK hD with hfin | hinf
  · left
    have hfwd := ae_firstRegenerationTime_forward Q.measure K hK.1 Δ hΔ lam R h₀
      (div_pos hl h₀) i hK.2.2.2.2.2.1
    have hgood : ∀ᵐ q ∂μ, RecordCanShift Δ lam R i (iteratedRecord Δ lam R i 0 q) := by
      filter_upwards [hfin, hfwd] with q hq hforward
      change RecordCanShift Δ lam R i (futureRecord Δ R q.1 q.2 i 0)
      rw [recordCanShift_futureRecord_iff, sampleTimeShift_zero, zero_add]
      exact ⟨hq, hforward hq⟩
    have hcond := sbx_s6_conditional_first_law hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁
      P K hK hD
    have hiter := iteratedRecord_law_of_first_and_conditional_law Δ hΔ lam R i μ ν
      hνμ hgood hfirst hcond
    intro k hk
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    exact (hiter j).2
  · right
    have hAm : MeasurableSet {y : FutureState d i R |
        firstRegenerationTime Δ lam R (recordSample y) i = ⊤} :=
      measurableSet_eq_fun
        ((measurable_firstRegenerationTime Δ lam R i).comp (measurable_recordSample i R))
        measurable_const
    have hσinf : ∀ᵐ y ∂ν.map (iteratedRecord Δ lam R i 0),
        firstRegenerationTime Δ lam R (recordSample y) i = ⊤ := by
      apply (ae_map_iff (measurable_iteratedRecord Δ lam R i 0).aemeasurable hAm).mpr
      filter_upwards [hinf] with q hq
      change firstRegenerationTime Δ lam R
        (recordSample (regenerationRecord hd lam l 0 q)) i = ⊤
      rwa [sbx_s6_zero_record_first_time hd lam l q]
    rw [← hfirst] at hσinf
    have hnext : ∀ᵐ q ∂μ,
        firstRegenerationTime Δ lam R (recordSample (iteratedRecord Δ lam R i 1 q)) i = ⊤ :=
      ae_of_ae_map (measurable_iteratedRecord Δ lam R i 1).aemeasurable hσinf
    intro k hk
    filter_upwards [hnext] with q hq
    have hshift : firstRegenerationTime Δ lam R
        (sampleTimeShift Δ q.2 (Regeneration.regenerationTime Δ lam R q.2 i 1).toNNReal) i = ⊤ := by
      change firstRegenerationTime Δ lam R
        (recenterSample (q.2.1 (Regeneration.regenerationTime Δ lam R q.2 i 1).toNNReal)
          (sampleTimeShift Δ q.2 (Regeneration.regenerationTime Δ lam R q.2 i 1).toNNReal)) i = ⊤ at hq
      rwa [firstRegenerationTime_recenterSample] at hq
    have htwo : Regeneration.regenerationTime Δ lam R q.2 i 2 = ⊤ := by
      by_cases ht : Regeneration.regenerationTime Δ lam R q.2 i 1 = ⊤
      · rw [Regeneration.regenerationTime, ht, ite_eq_left rfl]
      · rw [Regeneration.regenerationTime, ite_eq_right ht, hshift, add_top]
    have htop : ∀ j : ℕ, Regeneration.regenerationTime Δ lam R q.2 i (j + 2) = ⊤ := by
      intro j
      induction j with
      | zero => exact htwo
      | succ j hj =>
          rw [show j + 1 + 2 = (j + 2) + 1 by omega,
            Regeneration.regenerationTime, hj, ite_eq_left rfl]
    change futureRecord Δ R q.1 q.2 i
      (Regeneration.regenerationTime Δ lam R q.2 i k).toNNReal = futureRecord Δ R q.1 q.2 i 0
    rw [show k = (k - 2) + 2 by omega, htop]
    rfl

end AllScale

/-- The actual restricted-record shift is measurable and has the required
zero-to-first characterization under both source laws, at every admissible
scale. This statement does not assert invariance or later-cycle composition. -/
theorem sbx_s6_restricted_shift_first
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    ∃ Θ : FutureState d (Renewal.forceCoord hd) (l / lam) →
        FutureState d (Renewal.forceCoord hd) (l / lam),
      Measurable Θ ∧
      ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
        ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l 0 q) = regenerationRecord hd lam l 1 q := by
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  obtain ⟨D, hDm, hdecode⟩ := Probability.exists_future_halfSpace_decoder i R
  let Θ := shiftRestrictedRecord Δ lam R i D
  have hΘ : Measurable Θ := measurable_shiftRestrictedRecord Δ lam R i D hDm
  have hfwd := ae_firstRegenerationTime_forward Q.measure K hK.1 Δ hΔ lam R h₀
    (div_pos hl h₀) i hK.2.2.2.2.2.1
  have hstep : ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      Θ (regenerationRecord hd lam l 0 q) = regenerationRecord hd lam l 1 q := by
    filter_upwards [hfwd] with q hq
    have hforward : 0 ≤ q.2.1 (firstRegenerationTime Δ lam R q.2 i).toNNReal i -
        q.2.1 0 i := by
      by_cases hfin : firstRegenerationTime Δ lam R q.2 i = ⊤
      · simp only [hfin, ENNReal.toNNReal_top, sub_self, le_refl]
      · exact hq hfin
    have h := shiftRestrictedRecord_futureRecord Δ hΔ lam R i D hdecode q.1 q.2 0
      (by simpa only [Nat.cast_zero, zero_mul, zero_add, sampleTimeShift_zero] using hforward)
    change Θ (futureRecord Δ R q.1 q.2 i
      (Regeneration.regenerationTime Δ lam R q.2 i 0).toNNReal) =
      futureRecord Δ R q.1 q.2 i
        (Regeneration.regenerationTime Δ lam R q.2 i 1).toNNReal
    rw [Regeneration.regenerationTime_one]
    change Θ (futureRecord Δ R q.1 q.2 i 0) =
      futureRecord Δ R q.1 q.2 i (firstRegenerationTime Δ lam R q.2 i).toNNReal
    simpa only [Nat.cast_zero, zero_mul, zero_add, sampleTimeShift_zero] using h
  dsimp only
  refine ⟨Θ, hΘ, ?_⟩
  intro ρ hρ
  rcases Set.mem_insert_iff.mp hρ with rfl | hρ
  · exact hstep
  · obtain rfl := Set.mem_singleton_iff.mp hρ
    exact (EinsteinFull.regenerationConditionedLaw_absolutelyContinuous
      hd Q lam l K hK.1 hD).ae_le hstep

/-- The actual measurable first-record shift preserves the conditioned
zero-record law at every admissible scale, including the infinity fallback. -/
theorem sbx_s6_invariant_first_shift
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) :
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    ∃ Θ : FutureState d (Renewal.forceCoord hd) (l / lam) →
        FutureState d (Renewal.forceCoord hd) (l / lam),
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
        ∀ᵐ q ∂ρ, Θ (regenerationRecord hd lam l 0 q) = regenerationRecord hd lam l 1 q) ∧
      Measure.map Θ (Measure.map (regenerationRecord hd lam l 0) ν) =
        Measure.map (regenerationRecord hd lam l 0) ν := by
  obtain ⟨Θ, hΘ, hstep⟩ := sbx_s6_restricted_shift_first hd Q lam h₀ h₁ l δ hl P K hK hD
  refine ⟨Θ, hΘ, hstep, ?_⟩
  rw [Measure.map_map hΘ (EinsteinFull.measurable_regenerationRecord hd lam l 0)]
  exact (Measure.map_congr (hstep _ (by exact Or.inr rfl))).trans
    (sbx_s6_conditional_first_law hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD)

/-- Support only: the tail dependency proves finiteness above its own scale
threshold. Its quantifier order is retained; this is not an all-scale producer
for the unchanged condition-iterate target. -/
theorem sbx_s6_first_finite_large_scale
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K →
      ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
        firstRegenerationTime (Renewal.regenDelta lam) lam (l / lam) q.2
          (Renewal.forceCoord hd) ≠ ⊤ := by
  obtain ⟨l₀, hl₀, hsep₀, htail⟩ := htails d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep₀, ?_⟩
  intro l hll₀ δ hδ hδ₁ Q lam h₀ h₁ P K hK
  obtain ⟨c, C, a, M, hc, _hC, _ha, _hac, _hM, hbound⟩ := htail l hll₀ δ hδ hδ₁
  obtain ⟨_hD, _hhalf, htail', _hμexp, _hνexp⟩ := hbound Q lam h₀ h₁ P K hK
  apply firstRegenerationTime_ne_top_ae_of_tail Q.measure K (Renewal.regenDelta lam)
    lam (l / lam) c C hc h₀ (Renewal.forceCoord hd)
  intro t ht
  simpa only [EinsteinFull.regenerationTime, regenerationTime_one] using htail' t ht

/-- The supplied tails close both-law record iteration above their own
threshold. The threshold is retained, so this is not the arbitrary-scale root. -/
theorem sbx_s6_all_record_iteration_large_scale
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
    ∀ (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    ∀ (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0),
    let μ := annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, 1 ≤ k →
        ρ.map (regenerationRecord hd lam l k) = ν.map (regenerationRecord hd lam l 0)) ∧
    ∃ Θ : FutureState d (Renewal.forceCoord hd) (l / lam) →
        FutureState d (Renewal.forceCoord hd) (l / lam),
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      (ν.map (regenerationRecord hd lam l 0)).map Θ =
        ν.map (regenerationRecord hd lam l 0) := by
  obtain ⟨l₀, hl₀, hsep₀, hfinite⟩ := sbx_s6_first_finite_large_scale htails d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hsep₀, ?_⟩
  intro l hll₀ δ hδ hδ₁ Q lam h₀ h₁ P K hK hD
  have hl : 0 < l := hl₀.trans_le hll₀
  have hsep : r₀ < 2 * l := hsep₀.trans_le (mul_le_mul_of_nonneg_left hll₀ (by norm_num))
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hνμ : ν ≪ μ :=
    EinsteinFull.regenerationConditionedLaw_absolutelyContinuous hd Q lam l K hK.1 hD
  have hfin := hfinite l hll₀ δ hδ hδ₁ Q lam h₀ h₁ P K hK
  have hfwd := ae_firstRegenerationTime_forward Q.measure K hK.1 Δ hΔ lam R h₀
    (div_pos hl h₀) i hK.2.2.2.2.2.1
  have hgood : ∀ᵐ q ∂μ, RecordCanShift Δ lam R i (iteratedRecord Δ lam R i 0 q) := by
    filter_upwards [hfin, hfwd] with q hq hforward
    change RecordCanShift Δ lam R i (futureRecord Δ R q.1 q.2 i 0)
    rw [recordCanShift_futureRecord_iff, sampleTimeShift_zero, zero_add]
    exact ⟨hq, hforward hq⟩
  have hfirst : μ.map (iteratedRecord Δ lam R i 1) = ν.map (iteratedRecord Δ lam R i 0) :=
    sbx_s6_annealed_first_law hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
  have hcond : ν.map (iteratedRecord Δ lam R i 1) = ν.map (iteratedRecord Δ lam R i 0) :=
    sbx_s6_conditional_first_law hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD
  have hiter := iteratedRecord_law_of_first_and_conditional_law Δ hΔ lam R i μ ν
    hνμ hgood hfirst hcond
  have hlaws : ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × CoupledSample d))),
      ∀ k : ℕ, 1 ≤ k →
        ρ.map (regenerationRecord hd lam l k) = ν.map (regenerationRecord hd lam l 0) := by
    intro ρ hρ k hk
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      exact (hiter j).2
    · obtain rfl := Set.mem_singleton_iff.mp hρ
      exact sbx_s6_conditional_all_record_laws hindep hd Q lam h₀ h₁ l δ hl hsep hδ hδ₁ P K hK hD k
  obtain ⟨D, hDm, hdecode⟩ := Probability.exists_future_halfSpace_decoder i R
  let Θ := shiftRestrictedRecord Δ lam R i D
  have hΘ : Measurable Θ := measurable_shiftRestrictedRecord Δ lam R i D hDm
  have hσgood : ∀ᵐ y ∂ν.map (iteratedRecord Δ lam R i 0), RecordCanShift Δ lam R i y :=
    (ae_map_iff (measurable_iteratedRecord Δ lam R i 0).aemeasurable
      (measurableSet_recordCanShift Δ lam R i)).mpr (hνμ.ae_le hgood)
  have hstep : ∀ k : ℕ, ∀ᵐ q ∂μ,
      Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q := by
    intro k
    have hkgood : ∀ᵐ q ∂μ, RecordCanShift Δ lam R i (iteratedRecord Δ lam R i k q) := by
      cases k with
      | zero => exact hgood
      | succ j =>
          rw [← (hiter j).2] at hσgood
          exact ae_of_ae_map (measurable_iteratedRecord Δ lam R i (j + 1)).aemeasurable hσgood
    have hkfin : ∀ᵐ q ∂μ, Regeneration.regenerationTime Δ lam R q.2 i k ≠ ⊤ := by
      cases k with
      | zero => exact Filter.Eventually.of_forall fun _ => ENNReal.zero_ne_top
      | succ j => exact (hiter j).1
    filter_upwards [hkgood, hkfin] with q hq hqfin
    exact (iteratedRecord_succ_of_canShift Δ hΔ lam R i D hdecode q k hqfin hq).2.symm
  refine ⟨hlaws, Θ, hΘ, ?_, ?_⟩
  · intro ρ hρ k
    rcases Set.mem_insert_iff.mp hρ with rfl | hρ
    · exact hstep k
    · obtain rfl := Set.mem_singleton_iff.mp hρ
      exact hνμ.ae_le (hstep k)
  · rw [Measure.map_map hΘ (EinsteinFull.measurable_regenerationRecord hd lam l 0)]
    exact (Measure.map_congr (hνμ.ae_le (hstep 0))).trans hcond

#print axioms sbx_s6_first_finite_iff_conditioned_positive
#print axioms sbx_s6_annealed_iteration_dichotomy
#print axioms sbx_s6_all_record_iteration_large_scale
#print axioms sbx_s6_all_records_eq_zero_of_infinite
#print axioms sbx_s6_conditioned_shift_all
#print axioms sbx_s6_zero_record_first_time
#print axioms sbx_s6_infinity_record_law
#print axioms sbx_s6_conditioned_first_time_dichotomy
#print axioms sbx_s6_conditional_all_record_laws
#print axioms sbx_s6_invariant_first_shift
#print axioms sbx_s6_record_first_eq_zero_of_infinite
#print axioms sbx_s6_zero_record_no_return_iff
#print axioms sbx_s6_integral_eq_infinity_of_slice_zero
#print axioms sbx_s6_annealed_first_law
#print axioms sbx_s6_infinity_implies_no_return
#print axioms sbx_s6_centered_residual_both
#print axioms sbx_s6_conditional_first_integral
#print axioms sbx_s6_conditional_first_law
#print axioms sbx_s6_conditioned_slice_factor_v2
#print axioms sbx_s6_slice_factor_both
#print axioms sbx_s6_first_regeneration_slice_factor
#print axioms sbx_s6_annealed_first_marginal
#print axioms sbx_s6_restricted_shift_first
#print axioms sbx_s6_first_finite_large_scale

end EinsteinFull.Blueprint

#lint
