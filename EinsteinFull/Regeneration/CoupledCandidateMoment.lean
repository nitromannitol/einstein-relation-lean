import EinsteinFull.Regeneration.CandidateInnerBounds
import EinsteinFull.Blueprint.G1.Proofs.S3MRenewalGeom
import EinsteinRelation.Regeneration.CandidatePrefix

/-!
# Exponential moment of a candidate search under the split coupling

A candidate search started at a grid-valued time decided by the observed history,
at a level decided by the same history, has an exponential overshoot of its
successful candidate whose moment is bounded uniformly against every history
weight. The failed rounds decay geometrically by restarting the coupling at the
successive candidates, and the overshoot is dominated by their sum.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

attribute [local irreducible] firstRoundedCandidate roundedCandidateSequence passageSequence
  firstSuccessfulCandidate

/-- The set of samples whose bit at a measurable grid index is false is measurable. -/
theorem measurableSet_bit_at_false {α : Type*} [MeasurableSpace α] {d : ℕ}
    (f : α → CoupledSample d) (hf : Measurable f) (k : α → ℕ) (hk : Measurable k) :
    MeasurableSet {a : α | (f a).2 (k a) = false} := by
  have heq : {a : α | (f a).2 (k a) = false} =
      ⋃ n : ℕ, ({a : α | k a = n} ∩ {a : α | (f a).2 n = false}) := by
    ext a
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff]
    exact ⟨fun h => ⟨k a, rfl, h⟩, fun ⟨n, hn, h⟩ => hn ▸ h⟩
  rw [heq]
  refine MeasurableSet.iUnion fun n => (hk (measurableSet_singleton n)).inter ?_
  exact measurableSet_eq_fun ((measurable_pi_apply n).comp (measurable_snd.comp hf))
    measurable_const

theorem measurable_gridIndex (Δ : ℝ≥0) : Measurable (gridIndex Δ) := by
  unfold gridIndex
  exact Nat.measurable_floor.comp (measurable_coe_nnreal_real.div_const _)

/-- The failed-round weight is jointly measurable in the level and the sample. -/
theorem measurable_failedRoundWeight_joint {d : ℕ} (Δ : ℝ≥0) (lam R b : ℝ) (i : Fin d)
    (N : ℕ) :
    Measurable (fun p : ℝ × CoupledSample d => failedRoundWeight Δ lam R p.1 b i N p.2) := by
  have hC : ∀ j, Measurable (fun p : ℝ × CoupledSample d =>
      roundedCandidateSequence Δ lam R p.1 p.2 i j) :=
    fun j => measurable_roundedCandidateSequence Δ lam R i j
  simp only [failedRoundWeight]
  have hset : MeasurableSet {p : ℝ × CoupledSample d |
      roundedCandidateSequence Δ lam R p.1 p.2 i N ≠ ⊤ ∧
      ∀ j < N, p.2.2 (gridIndex Δ (roundedCandidateSequence Δ lam R p.1 p.2 i j).toNNReal) =
        false} := by
    have heq : {p : ℝ × CoupledSample d | ∀ j < N,
        p.2.2 (gridIndex Δ (roundedCandidateSequence Δ lam R p.1 p.2 i j).toNNReal) = false} =
        ⋂ j ∈ Finset.range N, {p : ℝ × CoupledSample d |
          p.2.2 (gridIndex Δ (roundedCandidateSequence Δ lam R p.1 p.2 i j).toNNReal) = false} := by
      ext p
      simp only [Set.mem_ofPred_eq, Set.mem_iInter, Finset.mem_range]
    have hbitset : MeasurableSet {p : ℝ × CoupledSample d | ∀ j < N,
        p.2.2 (gridIndex Δ (roundedCandidateSequence Δ lam R p.1 p.2 i j).toNNReal) = false} := by
      rw [heq]
      exact Finset.measurableSet_biInter _ fun j _ =>
        measurableSet_bit_at_false (fun p : ℝ × CoupledSample d => p.2) measurable_snd _
          ((measurable_gridIndex Δ).comp (hC j).ennreal_toNNReal)
    exact (measurableSet_eq_fun (hC N) measurable_const).compl.inter hbitset
  have hval : Measurable (fun p : ℝ × CoupledSample d => ENNReal.ofReal (Real.exp (b * lam *
      (p.2.1 (roundedCandidateSequence Δ lam R p.1 p.2 i N).toNNReal i - p.2.1 0 i -
        p.1 / lam)))) := by
    apply ENNReal.measurable_ofReal.comp
    apply Real.measurable_exp.comp
    apply measurable_const.mul
    have hev : Measurable (fun p : ℝ × CoupledSample d =>
        p.2.1 (roundedCandidateSequence Δ lam R p.1 p.2 i N).toNNReal) :=
      measurable_path_eval.comp ((hC N).ennreal_toNNReal.prodMk measurable_snd.fst)
    exact (((measurable_pi_apply i).comp hev).sub ((measurable_pi_apply i).comp
      ((continuous_eval_const 0).measurable.comp measurable_snd.fst))).sub
      (measurable_fst.div_const lam)
  exact (hval.indicator hset)

/-- Agreement of observed histories through a time at which the `N`th candidate has
occurred gives the same candidates and the same failed-round weight. -/
theorem failedRoundWeight_congr {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R L b : ℝ)
    (hlam : 0 < lam) (hR : 0 < R) (i : Fin d) (N n : ℕ) (w w' : CoupledSample d)
    (hag : HistoryAgree Δ n w w')
    (hle : roundedCandidateSequence Δ lam R L w i N ≤ (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    roundedCandidateSequence Δ lam R L w' i N = roundedCandidateSequence Δ lam R L w i N ∧
      failedRoundWeight Δ lam R L b i N w' = failedRoundWeight Δ lam R L b i N w := by
  have hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) ((n : ℝ≥0) * Δ), w.1 t = w'.1 t :=
    fun t ht => hag.1 t ht.2
  have hNfin : roundedCandidateSequence Δ lam R L w i N ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.coe_ne_top hle
  have hC : ∀ j ≤ N, roundedCandidateSequence Δ lam R L w' i j =
      roundedCandidateSequence Δ lam R L w i j := by
    intro j hj
    have hjle : roundedCandidateSequence Δ lam R L w i j ≤ (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
      rcases lt_or_eq_of_le hj with h | h
      · exact (roundedCandidateSequence_lt_of_lt Δ hΔ lam R L hlam hR w i h hNfin).le.trans hle
      · rw [h]
        exact hle
    exact (roundedCandidateSequence_eq_of_prefix Δ hΔ lam R L hR w w' i j _ hpre hjle).symm
  refine ⟨hC N le_rfl, ?_⟩
  have hbits : ∀ j < N, w'.2 (gridIndex Δ (roundedCandidateSequence Δ lam R L w' i j).toNNReal) =
      w.2 (gridIndex Δ (roundedCandidateSequence Δ lam R L w i j).toNNReal) := by
    intro j hj
    rw [hC j hj.le]
    have hlt := roundedCandidateSequence_lt_of_lt Δ hΔ lam R L hlam hR w i hj hNfin
    have hjfin : roundedCandidateSequence Δ lam R L w i j ≠ ⊤ := ne_top_of_lt hlt
    obtain ⟨k, hk⟩ := roundedCandidateSequence_mem_grid Δ hΔ lam R L w i j hjfin
    rw [hk, ENNReal.toNNReal_coe, gridIndex_mul Δ hΔ]
    have hkn : k < n := by
      have h2 := lt_of_lt_of_le hlt hle
      rw [hk] at h2
      have h3 : (k : ℝ≥0) * Δ < (n : ℝ≥0) * Δ := ENNReal.coe_lt_coe.mp h2
      exact_mod_cast lt_of_mul_lt_mul_right h3 zero_le
    exact (hag.2 k hkn).symm
  have hNle : (roundedCandidateSequence Δ lam R L w i N).toNNReal ≤ (n : ℝ≥0) * Δ := by
    apply ENNReal.coe_le_coe.mp
    rw [ENNReal.coe_toNNReal hNfin]
    exact hle
  have hval : w'.1 (roundedCandidateSequence Δ lam R L w' i N).toNNReal i - w'.1 0 i =
      w.1 (roundedCandidateSequence Δ lam R L w i N).toNNReal i - w.1 0 i := by
    rw [hC N le_rfl, ← hag.1 _ hNle, ← hag.1 0 zero_le]
  simp only [failedRoundWeight]
  have hmem : (w' ∈ {w : CoupledSample d | roundedCandidateSequence Δ lam R L w i N ≠ ⊤ ∧
      ∀ j < N, w.2 (gridIndex Δ (roundedCandidateSequence Δ lam R L w i j).toNNReal) = false}) ↔
      (w ∈ {w : CoupledSample d | roundedCandidateSequence Δ lam R L w i N ≠ ⊤ ∧
      ∀ j < N, w.2 (gridIndex Δ (roundedCandidateSequence Δ lam R L w i j).toNNReal) = false}) := by
    simp only [Set.mem_ofPred_eq, hC N le_rfl]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j hj => (hbits j hj) ▸ h2 j hj⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, fun j hj => (hbits j hj).trans (h2 j hj)⟩
  by_cases hw : w ∈ {w : CoupledSample d | roundedCandidateSequence Δ lam R L w i N ≠ ⊤ ∧
      ∀ j < N, w.2 (gridIndex Δ (roundedCandidateSequence Δ lam R L w i j).toNNReal) = false}
  · rw [Set.indicator_of_mem hw, Set.indicator_of_mem (hmem.mpr hw), hval]
  · rw [Set.indicator_of_notMem hw, Set.indicator_of_notMem (fun h => hw (hmem.mp h))]


theorem measurable_failedCoinWeight {d : ℕ} (Δ : ℝ≥0) (lam R b : ℝ) (i : Fin d) :
    Measurable (failedCoinWeight (d := d) Δ lam R b i) := by
  have hC : Measurable (fun v : CoupledSample d =>
      firstRoundedCandidate Δ lam R (3 * lam * R) v.1 i) :=
    (measurable_firstRoundedCandidate Δ lam R i).comp (measurable_const.prodMk measurable_fst)
  apply Measurable.indicator
  · apply ENNReal.measurable_ofReal.comp
    apply Real.measurable_exp.comp
    apply measurable_const.mul
    have hev : Measurable (fun v : CoupledSample d =>
        v.1 (firstRoundedCandidate Δ lam R (3 * lam * R) v.1 i).toNNReal) :=
      measurable_path_eval.comp (hC.ennreal_toNNReal.prodMk measurable_fst)
    exact ((measurable_pi_apply i).comp hev).sub
      ((measurable_pi_apply i).comp ((continuous_eval_const 0).measurable.comp measurable_fst))
  · exact (measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd)
      measurable_const).inter (measurableSet_eq_fun hC measurable_const).compl

/-- The time of the `N`th candidate of a search started at `T₀` at level `L₀`. -/
noncomputable def roundTime {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (T₀ : CoupledSample d → ℝ≥0∞) (L₀ : CoupledSample d → ℝ) (N : ℕ)
    (z : CoupledSample d) : ℝ≥0∞ :=
  if T₀ z = ⊤ then ⊤ else
    T₀ z + roundedCandidateSequence Δ lam R (L₀ z) (sampleTimeShift Δ z (T₀ z).toNNReal) i N

/-- The history weight after `N` failed rounds of a search started at `T₀`. -/
noncomputable def roundHistoryWeight {d : ℕ} (Δ : ℝ≥0) (lam R b : ℝ) (i : Fin d)
    (T₀ : CoupledSample d → ℝ≥0∞) (W₀ : CoupledSample d → ℝ≥0∞) (L₀ : CoupledSample d → ℝ)
    (N : ℕ) (z : CoupledSample d) : ℝ≥0∞ :=
  {z : CoupledSample d | T₀ z ≠ ⊤}.indicator (fun z => W₀ z *
    failedRoundWeight Δ lam R (L₀ z) b i N (sampleTimeShift Δ z (T₀ z).toNNReal)) z

theorem measurable_roundTime {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (T₀ : CoupledSample d → ℝ≥0∞) (hT₀ : Measurable T₀) (L₀ : CoupledSample d → ℝ)
    (hL₀ : Measurable L₀) (N : ℕ) : Measurable (roundTime Δ lam R i T₀ L₀ N) := by
  have hshift : Measurable (fun z : CoupledSample d => sampleTimeShift Δ z (T₀ z).toNNReal) :=
    (measurable_sampleTimeShift Δ).comp (hT₀.ennreal_toNNReal.prodMk measurable_id)
  exact Measurable.ite (measurableSet_eq_fun hT₀ measurable_const) measurable_const
    (hT₀.add ((measurable_roundedCandidateSequence Δ lam R i N).comp (hL₀.prodMk hshift)))

theorem measurable_roundHistoryWeight {d : ℕ} (Δ : ℝ≥0) (lam R b : ℝ) (i : Fin d)
    (T₀ : CoupledSample d → ℝ≥0∞) (hT₀ : Measurable T₀) (W₀ : CoupledSample d → ℝ≥0∞)
    (hW₀ : Measurable W₀) (L₀ : CoupledSample d → ℝ) (hL₀ : Measurable L₀) (N : ℕ) :
    Measurable (roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N) := by
  have hshift : Measurable (fun z : CoupledSample d => sampleTimeShift Δ z (T₀ z).toNNReal) :=
    (measurable_sampleTimeShift Δ).comp (hT₀.ennreal_toNNReal.prodMk measurable_id)
  exact (hW₀.mul ((measurable_failedRoundWeight_joint Δ lam R b i N).comp
    (hL₀.prodMk hshift))).indicator (measurableSet_eq_fun hT₀ measurable_const).compl

/-- One more failed round multiplies the history weight by the failed-coin weight of
the sample shifted to the round time. -/
theorem roundHistoryWeight_succ_le {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R b : ℝ) (i : Fin d)
    (T₀ : CoupledSample d → ℝ≥0∞)
    (hgrid₀ : ∀ z, T₀ z ≠ ⊤ → ∃ m : ℕ, T₀ z = (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞))
    (W₀ : CoupledSample d → ℝ≥0∞) (L₀ : CoupledSample d → ℝ) (N : ℕ) (z : CoupledSample d) :
    roundHistoryWeight Δ lam R b i T₀ W₀ L₀ (N + 1) z ≤
      {z : CoupledSample d | roundTime Δ lam R i T₀ L₀ N z ≠ ⊤}.indicator (fun z =>
        roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N z *
          failedCoinWeight Δ lam R b i
            (sampleTimeShift Δ z (roundTime Δ lam R i T₀ L₀ N z).toNNReal)) z := by
  by_cases hT : T₀ z = ⊤
  · simp only [roundHistoryWeight]
    rw [Set.indicator_of_notMem (show z ∉ {z : CoupledSample d | T₀ z ≠ ⊤} from fun h => h hT)]
    exact zero_le
  · obtain ⟨k, hk⟩ := hgrid₀ z hT
    set w := sampleTimeShift Δ z (T₀ z).toNNReal with hw
    have hsucc := failedRoundWeight_succ_le Δ lam R (L₀ z) b i N w
    by_cases hC : roundedCandidateSequence Δ lam R (L₀ z) w i N = ⊤
    · have hzero : failedRoundWeight Δ lam R (L₀ z) b i N w = 0 := by
        simp only [failedRoundWeight]
        exact Set.indicator_of_notMem (fun h => h.1 hC) _
      simp only [roundHistoryWeight]
      rw [Set.indicator_of_mem (show z ∈ {z : CoupledSample d | T₀ z ≠ ⊤} from hT)]
      rw [hzero, zero_mul] at hsucc
      rw [nonpos_iff_eq_zero.mp hsucc, mul_zero]
      exact zero_le
    · have hRT : roundTime Δ lam R i T₀ L₀ N z = T₀ z + roundedCandidateSequence Δ lam R (L₀ z) w i N := by
        simp only [roundTime, ite_eq_right hT, hw]
      have hRTfin : roundTime Δ lam R i T₀ L₀ N z ≠ ⊤ := by
        rw [hRT]
        exact ENNReal.add_ne_top.mpr ⟨hT, hC⟩
      have hshift : sampleTimeShift Δ z (roundTime Δ lam R i T₀ L₀ N z).toNNReal =
          sampleTimeShift Δ w (roundedCandidateSequence Δ lam R (L₀ z) w i N).toNNReal := by
        rw [hRT, ENNReal.toNNReal_add hT hC, hw, hk, ENNReal.toNNReal_coe]
        exact EinsteinFull.Blueprint.sampleTimeShift_add_grid Δ hΔ z k _
      simp only [roundHistoryWeight]
      rw [Set.indicator_of_mem (show z ∈ {z : CoupledSample d | roundTime Δ lam R i T₀ L₀ N z ≠ ⊤}
          from hRTfin),
        Set.indicator_of_mem (show z ∈ {z : CoupledSample d | T₀ z ≠ ⊤} from hT),
        Set.indicator_of_mem (show z ∈ {z : CoupledSample d | T₀ z ≠ ⊤} from hT), hshift,
        mul_assoc]
      gcongr

end EinsteinFull.Regeneration
