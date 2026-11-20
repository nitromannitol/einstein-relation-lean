import EinsteinFull.Regeneration.CandidateRounds
import EinsteinFull.Regeneration.AnnealedHistoryRestart
import EinsteinFull.Regeneration.UniformFirstCandidate

/-!
# Restarted bounds for the rounds of a candidate search

At almost every grid endpoint of the annealed split coupling, the coupled law has the
reduced diffusion as path marginal and a fresh coin at time zero. Hence the first
round of a candidate search has the exponential moment of the first rounded
candidate, and a failed coin followed by a new round has weight at most the average
of the failure probability `1 - δ` and the second moment of the new round.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

attribute [local irreducible] firstRoundedCandidate roundedCandidateSequence passageSequence

/-- A property of the quenched coupled law at the origin for almost every environment
and at almost every spatial start holds at almost every grid endpoint of the annealed
coupled law. -/
theorem ae_grid_endpoint_of_origin_and_product {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (p : Vec d × FieldPair d → Prop)
    (horigin : ∀ᵐ ω ∂Q.measure, p (0, ω))
    (hprod : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure, p xω) (m : ℕ) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      p (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) := by
  by_cases hm : m = 0
  · subst m
    have hs := ae_origin_start_of_isGMPReducedKernel hd Q lam h0.le h1 P K hK.1 hK.2.1 hK.2.2.1
    have hqmp : Measure.QuasiMeasurePreserving
        (Prod.fst : FieldPair d × CoupledSample d → FieldPair d)
        (annealedCoupledLaw Q.measure K) Q.measure := by
      refine ⟨measurable_fst, ?_⟩
      rw [EinsteinFull.Blueprint.c10_s3_annealed_environment_map Q K hK.1]
    filter_upwards [hs, hqmp.ae horigin] with q hq hp
    simpa only [Nat.cast_zero, zero_mul, hq] using hp
  · have hΔ : 0 < Renewal.regenDelta lam := EinsteinRelation.regenDelta_pos h0
    have ht : 0 < (m : ℝ≥0) * Renewal.regenDelta lam :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hΔ
    exact ae_at_endpoint_of_product_ae hd Q lam h0.le h1 P K hK.1 hK.2.1 hK.2.2.1 _ ht _ hprod

/-- The exponential height of a first rounded candidate, as a path functional. -/
noncomputable def firstCandidateWeight {d : ℕ} (Δ : ℝ≥0) (lam R L b : ℝ) (i : Fin d)
    (γ : Path d) : ℝ≥0∞ :=
  {γ : Path d | firstRoundedCandidate Δ lam R L γ i ≠ ⊤}.indicator
    (fun γ => ENNReal.ofReal (Real.exp (b * lam *
      (γ (firstRoundedCandidate Δ lam R L γ i).toNNReal i - γ 0 i - L / lam)))) γ

theorem failedRoundWeight_zero {d : ℕ} (Δ : ℝ≥0) (lam R L b : ℝ) (i : Fin d)
    (w : CoupledSample d) :
    failedRoundWeight Δ lam R L b i 0 w = firstCandidateWeight Δ lam R L b i w.1 := by
  have h0 : roundedCandidateSequence Δ lam R L w i 0 = firstRoundedCandidate Δ lam R L w.1 i := by
    simp only [roundedCandidateSequence]
  have hset : {w' : CoupledSample d | roundedCandidateSequence Δ lam R L w' i 0 ≠ ⊤ ∧
      ∀ j < 0, w'.2 (gridIndex Δ (roundedCandidateSequence Δ lam R L w' i j).toNNReal) = false} =
      {w' : CoupledSample d | firstRoundedCandidate Δ lam R L w'.1 i ≠ ⊤} := by
    ext w'
    simp only [Set.mem_ofPred_eq, Nat.not_lt_zero, IsEmpty.forall_iff, implies_true, and_true]
    simp only [roundedCandidateSequence]
  simp only [failedRoundWeight, firstCandidateWeight, hset]
  by_cases h : firstRoundedCandidate Δ lam R L w.1 i ≠ ⊤
  · rw [Set.indicator_of_mem (show w ∈ {w' : CoupledSample d |
        firstRoundedCandidate Δ lam R L w'.1 i ≠ ⊤} from h),
      Set.indicator_of_mem (show w.1 ∈ {γ : Path d | firstRoundedCandidate Δ lam R L γ i ≠ ⊤}
        from h), h0]
  · rw [Set.indicator_of_notMem (show w ∉ {w' : CoupledSample d |
        firstRoundedCandidate Δ lam R L w'.1 i ≠ ⊤} from h),
      Set.indicator_of_notMem (show w.1 ∉ {γ : Path d | firstRoundedCandidate Δ lam R L γ i ≠ ⊤}
        from h)]

theorem measurable_firstCandidateWeight {d : ℕ} (Δ : ℝ≥0) (lam R b : ℝ) (i : Fin d) :
    Measurable (fun p : ℝ × Path d => firstCandidateWeight Δ lam R p.1 b i p.2) := by
  have hC : Measurable (fun p : ℝ × Path d => firstRoundedCandidate Δ lam R p.1 p.2 i) :=
    measurable_firstRoundedCandidate Δ lam R i
  apply Measurable.indicator
  · apply ENNReal.measurable_ofReal.comp
    apply Real.measurable_exp.comp
    apply measurable_const.mul
    have hev : Measurable (fun p : ℝ × Path d => p.2 (firstRoundedCandidate Δ lam R p.1 p.2 i).toNNReal) :=
      continuous_eval.measurable.comp (measurable_snd.prodMk hC.ennreal_toNNReal)
    exact (((measurable_pi_apply i).comp hev).sub
      ((measurable_pi_apply i).comp ((continuous_eval_const 0).measurable.comp measurable_snd))).sub
      (measurable_fst.div_const lam)
  · exact (measurableSet_eq_fun hC measurable_const).compl


/-- At almost every grid endpoint, the first round of a candidate search has the
exponential moment of the first rounded candidate of the reduced diffusion. -/
theorem inner_first_round_le {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (R b D : ℝ) (i : Fin d)
    (hP1 : ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (L : ℝ), 0 ≤ L →
      ∫⁻ γ, firstCandidateWeight (Renewal.regenDelta lam) lam R L b i γ ∂P (x, ω) ≤
        ENNReal.ofReal D) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (m : ℕ) (L : ℝ), 0 ≤ L →
      ∫⁻ w, failedRoundWeight (Renewal.regenDelta lam) lam R L b i 0 w
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal D := by
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.fst : FieldPair d × CoupledSample d → FieldPair d)
      (annealedCoupledLaw Q.measure K) Q.measure := by
    refine ⟨measurable_fst, ?_⟩
    rw [EinsteinFull.Blueprint.c10_s3_annealed_environment_map Q K hK.1]
  rw [ae_all_iff]
  intro m
  filter_upwards [EinsteinFull.Blueprint.c10_s3_grid_endpoint_path_marginal hd Q lam h0 h1 l δ
    P K hK m, hqmp.ae hP1] with q hmarg hb
  intro L hL
  simp only [failedRoundWeight_zero]
  have hmeas : Measurable (fun γ : Path d =>
      firstCandidateWeight (Renewal.regenDelta lam) lam R L b i γ) :=
    (measurable_firstCandidateWeight (Renewal.regenDelta lam) lam R b i).comp
      (measurable_const.prodMk measurable_id)
  calc ∫⁻ w, firstCandidateWeight (Renewal.regenDelta lam) lam R L b i w.1
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1)
      = ∫⁻ γ, firstCandidateWeight (Renewal.regenDelta lam) lam R L b i γ
        ∂(K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1)).map Prod.fst :=
        (lintegral_map hmeas measurable_fst).symm
    _ = ∫⁻ γ, firstCandidateWeight (Renewal.regenDelta lam) lam R L b i γ
        ∂P (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) := by rw [hmarg]
    _ ≤ ENNReal.ofReal D := hb _ L hL

/-- The squared weight of the first rounded candidate of a search at level `3R`. -/
noncomputable def squaredRestartWeight {d : ℕ} (Δ : ℝ≥0) (lam R b : ℝ) (i : Fin d)
    (γ : Path d) : ℝ≥0∞ :=
  {γ : Path d | firstRoundedCandidate Δ lam R (3 * lam * R) γ i ≠ ⊤}.indicator
    (fun γ => ENNReal.ofReal (Real.exp (2 * (b * lam *
      (γ (firstRoundedCandidate Δ lam R (3 * lam * R) γ i).toNNReal i - γ 0 i))))) γ

theorem measurable_squaredRestartWeight {d : ℕ} (Δ : ℝ≥0) (lam R b : ℝ) (i : Fin d) :
    Measurable (squaredRestartWeight (d := d) Δ lam R b i) := by
  have hC : Measurable (fun γ : Path d => firstRoundedCandidate Δ lam R (3 * lam * R) γ i) :=
    (measurable_firstRoundedCandidate Δ lam R i).comp (measurable_const.prodMk measurable_id)
  apply Measurable.indicator
  · apply ENNReal.measurable_ofReal.comp
    apply Real.measurable_exp.comp
    apply measurable_const.mul
    apply measurable_const.mul
    have hev : Measurable (fun γ : Path d =>
        γ (firstRoundedCandidate Δ lam R (3 * lam * R) γ i).toNNReal) :=
      continuous_eval.measurable.comp (measurable_id.prodMk hC.ennreal_toNNReal)
    exact ((measurable_pi_apply i).comp hev).sub
      ((measurable_pi_apply i).comp (continuous_eval_const 0).measurable)
  · exact (measurableSet_eq_fun hC measurable_const).compl

/-- A failed-coin weight is at most the average of the failed-coin indicator and the
squared restart weight. -/
theorem failedCoinWeight_le_half {d : ℕ} (Δ : ℝ≥0) (lam R b : ℝ) (i : Fin d)
    (v : CoupledSample d) :
    failedCoinWeight Δ lam R b i v ≤ ENNReal.ofReal (1 / 2) *
      ({v : CoupledSample d | v.2 0 = false}.indicator 1 v +
        squaredRestartWeight Δ lam R b i v.1) := by
  by_cases hv : v.2 0 = false ∧ firstRoundedCandidate Δ lam R (3 * lam * R) v.1 i ≠ ⊤
  · simp only [failedCoinWeight, squaredRestartWeight]
    rw [Set.indicator_of_mem (show v ∈ {v : CoupledSample d | v.2 0 = false ∧
        firstRoundedCandidate Δ lam R (3 * lam * R) v.1 i ≠ ⊤} from hv),
      Set.indicator_of_mem (show v ∈ {v : CoupledSample d | v.2 0 = false} from hv.1),
      Set.indicator_of_mem (show v.1 ∈ {γ : Path d |
        firstRoundedCandidate Δ lam R (3 * lam * R) γ i ≠ ⊤} from hv.2), Pi.one_apply,
      ← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (Real.exp_pos _).le,
      ← ENNReal.ofReal_mul (by norm_num)]
    apply ENNReal.ofReal_le_ofReal
    set x := b * lam * (v.1 (firstRoundedCandidate Δ lam R (3 * lam * R) v.1 i).toNNReal i -
      v.1 0 i)
    have hsq : Real.exp (2 * x) = Real.exp x ^ 2 := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [hsq]
    nlinarith [sq_nonneg (Real.exp x - 1)]
  · simp only [failedCoinWeight]
    rw [Set.indicator_of_notMem (show v ∉ {v : CoupledSample d | v.2 0 = false ∧
        firstRoundedCandidate Δ lam R (3 * lam * R) v.1 i ≠ ⊤} from hv)]
    exact zero_le

/-- A probability law of the coupled sample with a fresh first coin gives the coin
the value false with probability `1 - δ`. -/
theorem measure_firstBit_false {d : ℕ} (Δ : ℝ≥0) (δ : ℝ)
    (K : CoupledQuenchedLaws d) (xω : Vec d × FieldPair d) [IsProbabilityMeasure (K xω)]
    (hfresh : FreshBitsAt Δ δ K xω) :
    K xω {v : CoupledSample d | v.2 0 = false} = ENNReal.ofReal (1 - δ) := by
  have hbit : Measurable (fun v : CoupledSample d => v.2 0) :=
    (measurable_pi_apply 0).comp measurable_snd
  have htrue_meas : MeasurableSet {v : CoupledSample d | v.2 0 = true} :=
    measurableSet_eq_fun hbit measurable_const
  have h := hfresh 0 (fun _ => 1) measurable_const ⟨1, fun _ => by simp⟩
  have hu : (K xω).real Set.univ = 1 := by simp [measureReal_def]
  simp only [one_mul, integral_const, hu, smul_eq_mul, mul_one] at h
  have hind : (fun v : CoupledSample d => if v.2 0 = true then (1 : ℝ) else 0) =
      {v : CoupledSample d | v.2 0 = true}.indicator 1 := by
    funext v
    by_cases hv : v.2 0 = true <;> simp [hv]
  rw [hind, integral_indicator_one htrue_meas] at h
  have hδ0 : 0 ≤ δ := h ▸ measureReal_nonneg
  have htrue : K xω {v : CoupledSample d | v.2 0 = true} = ENNReal.ofReal δ := by
    rw [← h, measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)]
  have hcompl : {v : CoupledSample d | v.2 0 = false} = {v : CoupledSample d | v.2 0 = true}ᶜ := by
    ext v
    simp
  rw [hcompl, prob_compl_eq_one_sub htrue_meas, htrue, ENNReal.ofReal_sub _ hδ0,
    ENNReal.ofReal_one]

/-- At almost every grid endpoint, a failed coin followed by a new round has weight at
most the average of `1 - δ` and the second moment of the new round. -/
theorem inner_failed_coin_le {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (R b E : ℝ) (i : Fin d)
    (hP2 : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      ∫⁻ γ, squaredRestartWeight (Renewal.regenDelta lam) lam R b i γ ∂P (x, ω) ≤
        ENNReal.ofReal E) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      ∫⁻ v, failedCoinWeight (Renewal.regenDelta lam) lam R b i v
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤
        ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (1 - δ) + ENNReal.ofReal E) := by
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.fst : FieldPair d × CoupledSample d → FieldPair d)
      (annealedCoupledLaw Q.measure K) Q.measure := by
    refine ⟨measurable_fst, ?_⟩
    rw [EinsteinFull.Blueprint.c10_s3_annealed_environment_map Q K hK.1]
  rw [ae_all_iff]
  intro m
  have hgood := ae_grid_endpoint_of_origin_and_product hd Q lam h0 h1 l δ P K hK
    (fun xω => IsProbabilityMeasure (K xω) ∧ FreshBitsAt (Renewal.regenDelta lam) δ K xω)
    (by filter_upwards [hK.1.1, hK.2.2.2.1.1] with ω hp hf using ⟨hp, hf⟩)
    (by filter_upwards [hK.1.2, hK.2.2.2.1.2] with xω hp hf using ⟨hp, hf⟩) m
  filter_upwards [hgood, EinsteinFull.Blueprint.c10_s3_grid_endpoint_path_marginal hd Q lam h0 h1
    l δ P K hK m, hqmp.ae hP2] with q hq hmarg hb
  obtain ⟨hprob, hfresh⟩ := hq
  have hbitm : MeasurableSet {v : CoupledSample d | v.2 0 = false} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd) measurable_const
  have hsq : Measurable (squaredRestartWeight (d := d) (Renewal.regenDelta lam) lam R b i) :=
    measurable_squaredRestartWeight _ lam R b i
  calc ∫⁻ v, failedCoinWeight (Renewal.regenDelta lam) lam R b i v
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1)
      ≤ ∫⁻ v, ENNReal.ofReal (1 / 2) *
          ({v : CoupledSample d | v.2 0 = false}.indicator 1 v +
            squaredRestartWeight (Renewal.regenDelta lam) lam R b i v.1)
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) :=
        lintegral_mono fun v => failedCoinWeight_le_half _ lam R b i v
    _ = ENNReal.ofReal (1 / 2) *
          (K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) {v | v.2 0 = false} +
            ∫⁻ γ, squaredRestartWeight (Renewal.regenDelta lam) lam R b i γ
              ∂P (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left (measurable_one.indicator hbitm), lintegral_indicator_one hbitm,
          ← hmarg, lintegral_map hsq measurable_fst]
    _ ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (1 - δ) + ENNReal.ofReal E) := by
        rw [measure_firstBit_false _ δ K _ hfresh]
        gcongr
        exact hb _

end EinsteinFull.Regeneration
