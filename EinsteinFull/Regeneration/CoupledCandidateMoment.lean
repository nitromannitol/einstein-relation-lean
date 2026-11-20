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


/-- The round time and the history weight after `N` rounds are decided by the observed
history at the round time, when the start, the weight and the level of the search are
decided by the history at the start. -/
theorem roundTime_historyDecided {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R b : ℝ)
    (hlam : 0 < lam) (hR : 0 < R) (i : Fin d)
    (T₀ : CoupledSample d → ℝ≥0∞)
    (hgrid₀ : ∀ z, T₀ z ≠ ⊤ → ∃ m : ℕ, T₀ z = (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞))
    (W₀ : CoupledSample d → ℝ≥0∞) (L₀ : CoupledSample d → ℝ)
    (hdec₀ : HistoryDecided Δ T₀ (fun z => (W₀ z, L₀ z))) (N : ℕ) {α : Type*} (c : α) :
    HistoryDecided Δ (roundTime Δ lam R i T₀ L₀ N)
      (fun z => (roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N z, c)) := by
  intro m z z' hag hT
  have hT₀ : T₀ z ≠ ⊤ := by
    intro htop
    simp only [roundTime, ite_eq_left htop] at hT
    exact ENNReal.coe_ne_top hT.symm
  obtain ⟨k, hk⟩ := hgrid₀ z hT₀
  set w := sampleTimeShift Δ z (T₀ z).toNNReal with hw
  have hwk : w = sampleTimeShift Δ z ((k : ℝ≥0) * Δ) := by rw [hw, hk, ENNReal.toNNReal_coe]
  have hRT : roundTime Δ lam R i T₀ L₀ N z = T₀ z + roundedCandidateSequence Δ lam R (L₀ z) w i N := by
    simp only [roundTime, ite_eq_right hT₀, hw]
  have hCfin : roundedCandidateSequence Δ lam R (L₀ z) w i N ≠ ⊤ := by
    intro htop
    rw [hRT, htop, add_top] at hT
    exact ENNReal.coe_ne_top hT.symm
  obtain ⟨j, hj⟩ := roundedCandidateSequence_mem_grid Δ hΔ lam R (L₀ z) w i N hCfin
  have hmkj : m = k + j := by
    have h : (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) = ((((k + j : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
      rw [← hT, hRT, hk, hj, ← ENNReal.coe_add]
      push_cast
      ring_nf
    exact grid_index_unique Δ hΔ h
  have hkm : k ≤ m := by omega
  obtain ⟨hT₀', hWL⟩ := hdec₀ k z z' (hag.mono hkm) hk
  simp only [Prod.mk.injEq] at hWL
  obtain ⟨hW, hL⟩ := hWL
  have hagw : HistoryAgree Δ j w (sampleTimeShift Δ z' ((k : ℝ≥0) * Δ)) := by
    have h := hag.shift hΔ hkm
    rw [show m - k = j by omega] at h
    rw [hwk]
    exact h
  have hwk' : sampleTimeShift Δ z' (T₀ z').toNNReal = sampleTimeShift Δ z' ((k : ℝ≥0) * Δ) := by
    rw [hT₀', hk, ENNReal.toNNReal_coe]
  obtain ⟨hCeq, hFeq⟩ := failedRoundWeight_congr Δ hΔ lam R (L₀ z) b hlam hR i N j w _ hagw
    (le_of_eq hj)
  have hRT' : roundTime Δ lam R i T₀ L₀ N z' = roundTime Δ lam R i T₀ L₀ N z := by
    have hT₀'ne : T₀ z' ≠ ⊤ := hT₀' ▸ hT₀
    rw [hRT]
    simp only [roundTime, ite_eq_right hT₀'ne]
    rw [hwk', hL, hCeq, hT₀']
  refine ⟨hRT', ?_⟩
  simp only [Prod.mk.injEq, and_true]
  have hT₀'ne : T₀ z' ≠ ⊤ := hT₀' ▸ hT₀
  simp only [roundHistoryWeight]
  rw [Set.indicator_of_mem (show z' ∈ {z : CoupledSample d | T₀ z ≠ ⊤} from hT₀'ne),
    Set.indicator_of_mem (show z ∈ {z : CoupledSample d | T₀ z ≠ ⊤} from hT₀), hW, hL, hwk', hFeq]

/-- The history weights of the failed rounds decay geometrically. -/
theorem lintegral_roundHistoryWeight_le {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (R b D ρ : ℝ) (hR : 0 < R) (i : Fin d)
    (h1st : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (m : ℕ) (L : ℝ), 0 ≤ L →
      ∫⁻ w, failedRoundWeight (Renewal.regenDelta lam) lam R L b i 0 w
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal D)
    (hcoin : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      ∫⁻ v, failedCoinWeight (Renewal.regenDelta lam) lam R b i v
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal ρ)
    (T₀ : CoupledSample d → ℝ≥0∞) (hT₀ : Measurable T₀)
    (hgrid₀ : ∀ z, T₀ z ≠ ⊤ → ∃ m : ℕ,
      T₀ z = (((m : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞))
    (W₀ : CoupledSample d → ℝ≥0∞) (hW₀ : Measurable W₀)
    (L₀ : CoupledSample d → ℝ) (hL₀m : Measurable L₀) (hL₀ : ∀ z, 0 ≤ L₀ z)
    (hdec₀ : HistoryDecided (Renewal.regenDelta lam) T₀ (fun z => (W₀ z, L₀ z))) (N : ℕ) :
    ∫⁻ q, roundHistoryWeight (Renewal.regenDelta lam) lam R b i T₀ W₀ L₀ N q.2
        ∂annealedCoupledLaw Q.measure K ≤
      ENNReal.ofReal ρ ^ N * ENNReal.ofReal D *
        ∫⁻ q, {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2) q
          ∂annealedCoupledLaw Q.measure K := by
  let Δ := Renewal.regenDelta lam
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  induction N with
  | zero =>
    have h := lintegral_grid_stopping_le_of_decided hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
      T₀ hT₀ hgrid₀ W₀ hW₀
      (fun p => failedRoundWeight Δ lam R (L₀ p.1) b i 0 p.2)
      ((measurable_failedRoundWeight_joint Δ lam R b i 0).comp
        ((hL₀m.comp measurable_fst).prodMk measurable_snd))
      (by
        intro m z z' hag hz
        obtain ⟨hT, hWL⟩ := hdec₀ m z z' hag hz
        simp only [Prod.mk.injEq] at hWL
        refine ⟨hT, ?_⟩
        simp only [hWL.1, hWL.2])
      (ENNReal.ofReal D)
      (by
        filter_upwards [h1st] with q hq m _
        exact hq m (L₀ q.2) (hL₀ q.2))
    simp only [pow_zero, one_mul]
    exact h
  | succ N ih =>
    let TN := roundTime Δ lam R i T₀ L₀ N
    let WN := roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N
    have hTN : Measurable TN := measurable_roundTime Δ lam R i T₀ hT₀ L₀ hL₀m N
    have hWN : Measurable WN := measurable_roundHistoryWeight Δ lam R b i T₀ hT₀ W₀ hW₀ L₀ hL₀m N
    have hgridN : ∀ z, TN z ≠ ⊤ → ∃ m : ℕ, TN z = (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
      intro z hz
      have hT₀z : T₀ z ≠ ⊤ := by
        intro htop
        apply hz
        simp only [TN, roundTime, ite_eq_left htop]
      obtain ⟨k, hk⟩ := hgrid₀ z hT₀z
      have hRT : TN z = T₀ z + roundedCandidateSequence Δ lam R (L₀ z)
          (sampleTimeShift Δ z (T₀ z).toNNReal) i N := by
        simp only [TN, roundTime, ite_eq_right hT₀z]
      have hCfin : roundedCandidateSequence Δ lam R (L₀ z)
          (sampleTimeShift Δ z (T₀ z).toNNReal) i N ≠ ⊤ := by
        intro htop
        apply hz
        rw [hRT, htop, add_top]
      obtain ⟨j, hj⟩ := roundedCandidateSequence_mem_grid Δ hΔ lam R (L₀ z) _ i N hCfin
      refine ⟨k + j, ?_⟩
      rw [hRT, hj, hk, ← ENNReal.coe_add]
      congr 1
      push_cast
      simp only [Δ]
      ring
    have hdecN := roundTime_historyDecided Δ hΔ lam R b h0 hR i T₀ hgrid₀ W₀ L₀ hdec₀ N
      (fun w : CoupledSample d => failedCoinWeight Δ lam R b i w)
    have hrest := lintegral_grid_stopping_le_of_decided hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
      TN hTN hgridN WN hWN (fun p => failedCoinWeight Δ lam R b i p.2)
      ((measurable_failedCoinWeight Δ lam R b i).comp measurable_snd) hdecN (ENNReal.ofReal ρ)
      (by
        filter_upwards [hcoin] with q hq m _
        exact hq m)
    calc ∫⁻ q, roundHistoryWeight Δ lam R b i T₀ W₀ L₀ (N + 1) q.2 ∂annealedCoupledLaw Q.measure K
        ≤ ∫⁻ q, {q : FieldPair d × CoupledSample d | TN q.2 ≠ ⊤}.indicator
            (fun q => WN q.2 * failedCoinWeight Δ lam R b i
              (sampleTimeShift Δ q.2 (TN q.2).toNNReal)) q ∂annealedCoupledLaw Q.measure K := by
          apply lintegral_mono
          intro q
          exact roundHistoryWeight_succ_le Δ hΔ lam R b i T₀ hgrid₀ W₀ L₀ N q.2
      _ ≤ ENNReal.ofReal ρ * ∫⁻ q, {q : FieldPair d × CoupledSample d | TN q.2 ≠ ⊤}.indicator
            (fun q => WN q.2) q ∂annealedCoupledLaw Q.measure K := hrest
      _ ≤ ENNReal.ofReal ρ * ∫⁻ q, WN q.2 ∂annealedCoupledLaw Q.measure K := by
          gcongr with q
          exact Set.indicator_le_self _ _ q
      _ ≤ ENNReal.ofReal ρ * (ENNReal.ofReal ρ ^ N * ENNReal.ofReal D *
            ∫⁻ q, {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2) q
              ∂annealedCoupledLaw Q.measure K) := by gcongr
      _ = _ := by ring


/-- Countable sums of measurable extended nonnegative functions are measurable. -/
theorem measurable_tsum_ennreal {α : Type*} [MeasurableSpace α] {f : ℕ → α → ℝ≥0∞}
    (h : ∀ n, Measurable (f n)) : Measurable fun x => ∑' n, f n x := by
  simp_rw [ENNReal.tsum_eq_iSup_sum]
  exact .iSup fun s ↦ s.measurable_fun_sum fun n _ => h n

theorem measurable_candidateOvershootWeight_joint {d : ℕ} (Δ : ℝ≥0) (lam R b : ℝ) (i : Fin d) :
    Measurable (fun p : ℝ × CoupledSample d => candidateOvershootWeight Δ lam R p.1 b i p.2) := by
  have hF : Measurable (fun p : ℝ × CoupledSample d =>
      firstSuccessfulCandidate Δ lam R p.1 p.2 i) := measurable_firstSuccessfulCandidate Δ lam R i
  simp only [candidateOvershootWeight]
  apply Measurable.indicator
  · apply ENNReal.measurable_ofReal.comp
    apply Real.measurable_exp.comp
    apply measurable_const.mul
    have hev : Measurable (fun p : ℝ × CoupledSample d =>
        p.2.1 (firstSuccessfulCandidate Δ lam R p.1 p.2 i + Δ).toNNReal) :=
      measurable_path_eval.comp ((hF.add measurable_const).ennreal_toNNReal.prodMk
        measurable_snd.fst)
    exact (((measurable_pi_apply i).comp hev).sub ((measurable_pi_apply i).comp
      ((continuous_eval_const 0).measurable.comp measurable_snd.fst))).sub
      (measurable_fst.div_const lam)
  · exact (measurableSet_eq_fun hF measurable_const).compl

/-- The support of the successful bridges persists after a shift by a grid time. -/
theorem bridgeSupport_sampleTimeShift {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (i : Fin d) (R : ℝ)
    (z : CoupledSample d)
    (hz : ∀ n : ℕ, z.2 n = true → ∀ t : ℝ≥0,
      (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
        z.1 t ∈ couplingRegion i R (z.1 ((n : ℝ≥0) * Δ))) (k : ℕ) :
    ∀ n : ℕ, (sampleTimeShift Δ z ((k : ℝ≥0) * Δ)).2 n = true → ∀ t : ℝ≥0,
      (n : ℝ≥0) * Δ ≤ t → t ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ →
        (sampleTimeShift Δ z ((k : ℝ≥0) * Δ)).1 t ∈ couplingRegion i R
          ((sampleTimeShift Δ z ((k : ℝ≥0) * Δ)).1 ((n : ℝ≥0) * Δ)) := by
  intro n hn t ht1 ht2
  have hbit : z.2 (k + n) = true := by
    have h := hn
    change z.2 (gridIndex Δ ((k : ℝ≥0) * Δ) + n) = true at h
    rwa [gridIndex_mul Δ hΔ] at h
  change z.1 ((k : ℝ≥0) * Δ + t) ∈ couplingRegion i R (z.1 ((k : ℝ≥0) * Δ + (n : ℝ≥0) * Δ))
  have hbase : (k : ℝ≥0) * Δ + (n : ℝ≥0) * Δ = ((k + n : ℕ) : ℝ≥0) * Δ := by
    push_cast
    ring
  rw [hbase]
  apply hz (k + n) hbit
  · rw [← hbase]
    exact add_le_add le_rfl ht1
  · calc (k : ℝ≥0) * Δ + t ≤ (k : ℝ≥0) * Δ + ((n + 1 : ℕ) : ℝ≥0) * Δ := add_le_add le_rfl ht2
      _ = ((k + n + 1 : ℕ) : ℝ≥0) * Δ := by push_cast; ring

/-- The exponential overshoot of a candidate search under the split coupling has a
moment bounded against every history weight. -/
theorem lintegral_candidateOvershoot_le {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (b D ρ : ℝ) (hb : 0 ≤ b)
    (h1st : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (m : ℕ) (L : ℝ), 0 ≤ L →
      ∫⁻ w, failedRoundWeight (Renewal.regenDelta lam) lam (l / lam) L b (Renewal.forceCoord hd) 0 w
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal D)
    (hcoin : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      ∫⁻ v, failedCoinWeight (Renewal.regenDelta lam) lam (l / lam) b (Renewal.forceCoord hd) v
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal ρ)
    (T₀ : CoupledSample d → ℝ≥0∞) (hT₀ : Measurable T₀)
    (hgrid₀ : ∀ z, T₀ z ≠ ⊤ → ∃ m : ℕ,
      T₀ z = (((m : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞))
    (W₀ : CoupledSample d → ℝ≥0∞) (hW₀ : Measurable W₀)
    (L₀ : CoupledSample d → ℝ) (hL₀m : Measurable L₀) (hL₀ : ∀ z, 0 ≤ L₀ z)
    (hdec₀ : HistoryDecided (Renewal.regenDelta lam) T₀ (fun z => (W₀ z, L₀ z))) :
    ∫⁻ q, {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2 *
        candidateOvershootWeight (Renewal.regenDelta lam) lam (l / lam) (L₀ q.2) b
          (Renewal.forceCoord hd) (sampleTimeShift (Renewal.regenDelta lam) q.2 (T₀ q.2).toNNReal)) q
        ∂annealedCoupledLaw Q.measure K ≤
      ENNReal.ofReal (Real.exp (b * lam * (11 * (l / lam)))) *
        ((1 - ENNReal.ofReal ρ)⁻¹ * ENNReal.ofReal D *
          ∫⁻ q, {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2) q
            ∂annealedCoupledLaw Q.measure K) := by
  let Δ := Renewal.regenDelta lam
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  let R := l / lam
  have hR : 0 < R := div_pos hl h0
  let i := Renewal.forceCoord hd
  let μ := annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure Q.measure := Q.probability
  have hshift : Measurable (fun z : CoupledSample d => sampleTimeShift Δ z (T₀ z).toNNReal) :=
    (measurable_sampleTimeShift Δ).comp (hT₀.ennreal_toNNReal.prodMk measurable_id)
  have hLHSm : Measurable (fun q : FieldPair d × CoupledSample d =>
      {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2 *
        candidateOvershootWeight Δ lam R (L₀ q.2) b i (sampleTimeShift Δ q.2 (T₀ q.2).toNNReal)) q) :=
    ((hW₀.comp measurable_snd).mul ((measurable_candidateOvershootWeight_joint Δ lam R b i).comp
      ((hL₀m.comp measurable_snd).prodMk (hshift.comp measurable_snd)))).indicator
      (measurableSet_eq_fun (hT₀.comp measurable_snd) measurable_const).compl
  have hRHSm : Measurable (fun q : FieldPair d × CoupledSample d =>
      ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
        ∑' N, roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N q.2) :=
    measurable_const.mul (measurable_tsum_ennreal fun N =>
      (measurable_roundHistoryWeight Δ lam R b i T₀ hT₀ W₀ hW₀ L₀ hL₀m N).comp measurable_snd)
  have hpoint : ∀ᵐ q ∂μ,
      {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2 *
        candidateOvershootWeight Δ lam R (L₀ q.2) b i (sampleTimeShift Δ q.2 (T₀ q.2).toNNReal)) q ≤
      ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
        ∑' N, roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N q.2 := by
    apply Measure.ae_compProd_of_ae_ae (measurableSet_le hLHSm hRHSm)
    filter_upwards [hK.1.1, hK.2.2.2.2.2.1.1] with ω hprob hsupp
    have : IsProbabilityMeasure (originCoupledLaw K ω) := hprob
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
    filter_upwards [hsupp] with z hz
    by_cases hT : T₀ z = ⊤
    · simp only [Set.indicator, Set.mem_ofPred_eq, hT, ne_eq, not_true_eq_false, ite_false]
      exact zero_le
    · obtain ⟨k, hk⟩ := hgrid₀ z hT
      have hwk : sampleTimeShift Δ z (T₀ z).toNNReal = sampleTimeShift Δ z ((k : ℝ≥0) * Δ) := by
        rw [hk, ENNReal.toNNReal_coe]
      have hsuppw := bridgeSupport_sampleTimeShift Δ hΔ i R z hz k
      rw [← hwk] at hsuppw
      have hle := candidateOvershootWeight_le Δ hΔ lam R (L₀ z) b h0 hR hb i _ hsuppw
      simp only [Set.indicator, Set.mem_ofPred_eq, hT, ne_eq, not_false_eq_true, ite_true]
      simp only [roundHistoryWeight, Set.indicator, Set.mem_ofPred_eq, hT, ne_eq,
        not_false_eq_true, ite_true]
      calc W₀ z * candidateOvershootWeight Δ lam R (L₀ z) b i (sampleTimeShift Δ z (T₀ z).toNNReal)
          ≤ W₀ z * (ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
            ∑' N, failedRoundWeight Δ lam R (L₀ z) b i N (sampleTimeShift Δ z (T₀ z).toNNReal)) := by
            gcongr
        _ = _ := by
            rw [ENNReal.tsum_mul_left, mul_left_comm]
  have hρle : ∀ N, ∫⁻ q, roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N q.2 ∂μ ≤
      ENNReal.ofReal ρ ^ N * ENNReal.ofReal D *
        ∫⁻ q, {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2) q ∂μ :=
    fun N => lintegral_roundHistoryWeight_le hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK R b D ρ hR i
      h1st hcoin T₀ hT₀ hgrid₀ W₀ hW₀ L₀ hL₀m hL₀ hdec₀ N
  calc _ ≤ ∫⁻ q, ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
          ∑' N, roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N q.2 ∂μ := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
          ∑' N, ∫⁻ q, roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N q.2 ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_tsum fun N => ((measurable_roundHistoryWeight Δ lam R b i T₀ hT₀ W₀ hW₀ L₀
          hL₀m N).comp measurable_snd).aemeasurable
    _ ≤ ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
          ∑' N, ENNReal.ofReal ρ ^ N * (ENNReal.ofReal D *
            ∫⁻ q, {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2) q
              ∂μ) := by
        gcongr with N
        rw [← mul_assoc]
        exact hρle N
    _ = _ := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
        ring

end EinsteinFull.Regeneration
