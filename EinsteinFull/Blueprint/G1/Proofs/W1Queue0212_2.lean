import EinsteinFull.Blueprint.G1.node_rt_u3A_many_u2D_cycle_u2D_moment
import EinsteinFull.Blueprint.Roots.node_rt_u3A_factorization
import EinsteinFull.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.Blueprint.Foundation.node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transfer
import EinsteinRelation.Regeneration.RenewalFromSliceFactor

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration

/-- A grid shift composes both the actual path and the future coin sequence. -/
theorem many_cycle_sample_shift_add {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (z : CoupledSample d) (n : ℕ) (t : ℝ≥0) :
    sampleTimeShift Δ (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) t =
      sampleTimeShift Δ z ((n : ℝ≥0) * Δ + t) := by
  apply Prod.ext
  · ext u
    simp only [sampleTimeShift, pathTimeShift, ContinuousMap.coe_mk, add_assoc]
  · funext k
    simp only [sampleTimeShift, gridIndex_mul Δ hΔ, gridIndex_grid_add Δ hΔ,
      Nat.add_assoc]

/-- The literal iterated time depends only on coordinate increments and coins. -/
theorem many_cycle_time_congr_inc {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    {z w : CoupledSample d}
    (h : ∀ s t : ℝ≥0, w.1 s i - w.1 t i = z.1 s i - z.1 t i)
    (hb : w.2 = z.2) (j : ℕ) :
    Regeneration.regenerationTime Δ lam R w i j =
      Regeneration.regenerationTime Δ lam R z i j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    simp only [Regeneration.regenerationTime, ih]
    split
    · rfl
    · congr 1
      apply firstRegenerationTime_congr_inc
      · intro s t
        exact h _ _
      · exact congrArg (fun b : BernoulliSequence => fun n => b (gridIndex Δ
          (Regeneration.regenerationTime Δ lam R z i j).toNNReal + n)) hb

/-- Restart the actual recursion at its first finite grid time, retaining infinity. -/
theorem many_cycle_time_restart {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (i : Fin d) (z : CoupledSample d) (n : ℕ)
    (hn : Regeneration.regenerationTime Δ lam R z i 1 =
      (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) (j : ℕ) :
    Regeneration.regenerationTime Δ lam R z i (j + 1) =
      (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) +
        Regeneration.regenerationTime Δ lam R
          (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) i j := by
  induction j with
  | zero => simpa only [Regeneration.regenerationTime, add_zero] using hn
  | succ j ih =>
    let t := Regeneration.regenerationTime Δ lam R
      (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) i j
    by_cases ht : t = ⊤
    · have hi : Regeneration.regenerationTime Δ lam R z i (j + 1) = ⊤ := by
        rw [ih]
        change (_ : ℝ≥0∞) + t = ⊤
        rw [ht, add_top]
      rw [Regeneration.regenerationTime, if_pos hi,
        Regeneration.regenerationTime, if_pos ht, add_top]
    · have hi : Regeneration.regenerationTime Δ lam R z i (j + 1) ≠ ⊤ := by
        rw [ih]; exact ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ht⟩
      rw [regenerationTime_succ_eq Δ lam R z i (j + 1) hi, ih]
      rw [Regeneration.regenerationTime, if_neg ht,
        ENNReal.toNNReal_add ENNReal.coe_ne_top ht,
        ENNReal.toNNReal_coe, many_cycle_sample_shift_add Δ hΔ, add_assoc]

/-- Reading an actual future record preserves every remaining regeneration time. -/
theorem many_cycle_record_time {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (ω : FieldPair d) (z : CoupledSample d) (t : ℝ≥0) (j : ℕ) :
    Regeneration.regenerationTime Δ lam R
      (recordSample (futureRecord Δ R ω z i t)) i j =
      Regeneration.regenerationTime Δ lam R (sampleTimeShift Δ z t) i j := by
  apply many_cycle_time_congr_inc
  · intro s u
    change (z.1 (t + s) i - z.1 t i) - (z.1 (t + u) i - z.1 t i) =
      z.1 (t + s) i - z.1 (t + u) i
    ring
  · rfl

/-- Bounded real tests determine the finite slice law, hence also its
nonnegative extended integrals. -/
theorem many_cycle_lintegral_slice {α β : Type*} [MeasurableSpace α]
    [MeasurableSpace β] (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (X Y : α → β) (hX : Measurable X) (hY : Measurable Y)
    (S : Set α) (F : β → ℝ≥0∞) (hF : Measurable F)
    (hslice : ∀ f : β → ℝ, Measurable f → BoundedRealTest f →
      (∫ x in S, f (X x) ∂μ) = (μ S).toReal * ∫ x, f (Y x) ∂ν) :
    (∫⁻ x in S, F (X x) ∂μ) = μ S * ∫⁻ x, F (Y x) ∂ν := by
  letI : IsFiniteMeasure (μ S • ν.map Y) :=
    (ν.map Y).smul_finite (measure_ne_top μ S)
  have he : (μ.restrict S).map X = μ S • ν.map Y := by
    apply measure_eq_of_bounded_real_tests
    intro f hf hb
    rw [integral_map hX.aemeasurable hf.aestronglyMeasurable,
      integral_smul_measure, integral_map hY.aemeasurable hf.aestronglyMeasurable]
    exact hslice f hf hb
  rw [← lintegral_map hF hX, he, lintegral_smul_measure,
    lintegral_map hF hY, smul_eq_mul]

open EinsteinFull.Work.W5

/-- The exponential weight at time zero is one, even on paths with an
infinite first regeneration time. -/
theorem many_cycle_weight_zero {d : ℕ} (hd : 2 ≤ d) (lam l a : ℝ)
    (z : CoupledSample d) : regenerationExponentialWeight hd lam l a 0 z = 1 := by
  simp only [regenerationExponentialWeight, EinsteinFull.regenerationTime,
    Regeneration.regenerationTime, ENNReal.zero_ne_top, if_false, ENNReal.toReal_zero,
    mul_zero, Real.exp_zero, ENNReal.ofReal_one]

/-- On a finite first-time slice the literal weight splits, including the
infinite remaining-time branch. -/
theorem many_cycle_weight_restart {d : ℕ} (hd : 2 ≤ d) (lam l a : ℝ)
    (hlam : lam ≠ 0) (ω : FieldPair d) (z : CoupledSample d) (n j : ℕ)
    (hn : EinsteinFull.regenerationTime hd lam l 1 z =
      (((n : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)) :
    regenerationExponentialWeight hd lam l a (j + 1) z =
      ENNReal.ofReal (Real.exp (a * n)) * regenerationExponentialWeight hd lam l a j
        (recordSample (regenerationRecord hd lam l 1 (ω, z))) := by
  let Δ := Renewal.regenDelta lam
  let t := EinsteinFull.regenerationTime hd lam l j
    (sampleTimeShift Δ z ((n : ℝ≥0) * Δ))
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_ne_zero hlam))
  have hr := many_cycle_time_restart Δ hΔ lam (l / lam) (Renewal.forceCoord hd) z n hn j
  have hrec : EinsteinFull.regenerationTime hd lam l j
      (recordSample (regenerationRecord hd lam l 1 (ω, z))) = t := by
    change Regeneration.regenerationTime Δ lam (l / lam)
      (recordSample (futureRecord Δ (l / lam) ω z (Renewal.forceCoord hd)
        (EinsteinFull.regenerationTime hd lam l 1 z).toNNReal)) _ j = _
    rw [hn, ENNReal.toNNReal_coe]
    exact many_cycle_record_time _ _ _ _ _ _ _ _
  change EinsteinFull.regenerationTime hd lam l (j + 1) z = _ + t at hr
  unfold regenerationExponentialWeight
  rw [hr, hrec]
  by_cases ht : t = ⊤
  · rw [ht, add_top, if_pos rfl,
      ENNReal.mul_top (ne_of_gt (ENNReal.ofReal_pos.mpr (Real.exp_pos _)))]
  · rw [if_neg (ENNReal.add_ne_top.mpr ⟨ENNReal.coe_ne_top, ht⟩), if_neg ht,
      ENNReal.toReal_add ENNReal.coe_ne_top ht, mul_add, mul_assoc,
      regeneration_scaled_grid_time lam hlam n, Real.exp_add,
      ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- The first-time slice identity multiplies the actual remaining-cycle
moment, without assuming later-time finiteness or independence. -/
theorem many_cycle_moment_succ
    (hfac : node_rt_u3A_factorizationStmt)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hr : r₀ < 2 * l) (hδ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (μ : Measure (FieldPair d × CoupledSample d)) [IsFiniteMeasure μ]
    (hμ : μ ∈ ({annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} : Set (Measure _)))
    (hf : ∀ᵐ q ∂μ, EinsteinFull.regenerationTime hd lam l 1 q.2 ≠ ⊤)
    (a : ℝ) (j : ℕ) :
    (∫⁻ q, regenerationExponentialWeight hd lam l a (j + 1) q.2 ∂μ) =
      (∫⁻ q, regenerationExponentialWeight hd lam l a 1 q.2 ∂μ) *
      ∫⁻ q, regenerationExponentialWeight hd lam l a j q.2
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  letI : IsProbabilityMeasure ν := regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  let Δ := Renewal.regenDelta lam
  let S := fun n : ℕ => {q : FieldPair d × CoupledSample d |
    EinsteinFull.regenerationTime hd lam l 1 q.2 = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}
  let F := fun y : FutureState d (Renewal.forceCoord hd) (l / lam) =>
    regenerationExponentialWeight hd lam l a j (recordSample y)
  have hF : Measurable F := (measurable_regenerationExponentialWeight hd lam l a j).comp
    (measurable_recordSample _ _)
  have hX (k : ℕ) : Measurable (regenerationRecord hd lam l k) :=
    measurable_iteratedRecord _ _ _ _ _
  have htime : Measurable (fun q : FieldPair d × CoupledSample d =>
      EinsteinFull.regenerationTime hd lam l 1 q.2) :=
    (measurable_regenerationTime _ _ _ _ _).comp measurable_snd
  have hS (n : ℕ) : MeasurableSet (S n) := htime (measurableSet_singleton _)
  have hΔ : 0 < Δ := Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hdis : Pairwise (fun m n => Disjoint (S m) (S n)) := by
    intro m n hmn
    apply Set.disjoint_left.mpr
    intro q hm hn
    have H := mul_right_cancel₀ hΔ.ne' (ENNReal.coe_inj.mp (hm.symm.trans hn))
    exact hmn (by exact_mod_cast H)
  have hcover : ∀ᵐ q ∂μ, q ∈ ⋃ n, S n := by
    filter_upwards [hf] with q hq
    obtain ⟨n, hn⟩ := regenerationTime_mem_grid _ hΔ _ _ q.2 _ 1 hq
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hzero (q : FieldPair d × CoupledSample d) :
      F (regenerationRecord hd lam l 0 q) =
        regenerationExponentialWeight hd lam l a j q.2 := by
    have ht := many_cycle_record_time Δ lam (l / lam) (Renewal.forceCoord hd) q.1 q.2 0 j
    rw [sampleTimeShift_zero] at ht
    have ht' : EinsteinFull.regenerationTime hd lam l j
        (recordSample (regenerationRecord hd lam l 0 q)) =
        EinsteinFull.regenerationTime hd lam l j q.2 := ht
    dsimp only [F]
    unfold regenerationExponentialWeight
    rw [ht']
  have hslice (n : ℕ) : (∫⁻ q in S n, F (regenerationRecord hd lam l 1 q) ∂μ) =
      μ (S n) * ∫⁻ q, regenerationExponentialWeight hd lam l a j q.2 ∂ν := by
    rw [many_cycle_lintegral_slice μ ν _ _ (hX 1) (hX 0) (S n) F hF ?_]
    · simp_rw [hzero]
    · intro f hf hb
      have H := (hfac d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hr hδ hδ₁ P K hK hD).1
        (fun _ => 1) measurable_const ⟨1, by intro x; norm_num⟩ f hf hb n μ hμ
      simpa only [one_mul, integral_const, smul_eq_mul, measureReal_def,
        Measure.restrict_apply_univ, mul_one] using H
  calc
    _ = ∫⁻ q in ⋃ n, S n, regenerationExponentialWeight hd lam l a (j + 1) q.2 ∂μ := by
      rw [Measure.restrict_eq_self_of_ae_mem hcover]
    _ = ∑' n, ∫⁻ q in S n, regenerationExponentialWeight hd lam l a (j + 1) q.2 ∂μ :=
      lintegral_iUnion hS hdis _
    _ = ∑' n : ℕ, ENNReal.ofReal (Real.exp (a * n)) * μ (S n) *
        ∫⁻ q, regenerationExponentialWeight hd lam l a j q.2 ∂ν := by
      apply tsum_congr
      intro n
      rw [setLIntegral_congr_fun (hS n) (fun q hq =>
        many_cycle_weight_restart hd lam l a h₀.ne' q.1 q.2 n j hq)]
      change (∫⁻ q in S n, ENNReal.ofReal (Real.exp (a * n)) *
        F (regenerationRecord hd lam l 1 q) ∂μ) = _
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, hslice, mul_assoc]
    _ = (∑' n : ℕ, ENNReal.ofReal (Real.exp (a * n)) * μ (S n)) *
        ∫⁻ q, regenerationExponentialWeight hd lam l a j q.2 ∂ν := by
      rw [ENNReal.tsum_mul_right]
    _ = _ := by rw [← regeneration_exponentialMoment_eq_tsum hd lam l a h₀.ne' 1 μ hf]

/-- Moment multiplication for the literal regeneration times, using exactly
the three direct graph dependencies at `paper/main.tex:393`. -/
theorem node_rt_u3A_many_u2D_cycle_u2D_moment_of_deps
    (hfac : node_rt_u3A_factorizationStmt)
    (htails : node_app_u3A_regen_u2D_tailsStmt)
    (htransfer : node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transferStmt) :
    node_rt_u3A_many_u2D_cycle_u2D_momentStmt := by
  intro d hd Λ₀ r₀
  obtain ⟨lt, hlt, hrt, ht⟩ := htails d hd Λ₀ r₀
  obtain ⟨lp, _hlp, _hrp, _hp⟩ := htransfer d hd Λ₀ r₀
  refine ⟨max lt lp, hlt.trans_le (le_max_left _ _),
    hrt.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)), ?_⟩
  intro l hl δ hδ hδ₁
  obtain ⟨c, C, a, M, _hc, _hC, ha, _hac, hM, ht⟩ :=
    ht l ((le_max_left _ _).trans hl) δ hδ hδ₁
  refine ⟨a, max M 1, 1, ha, hM.trans_le (le_max_left _ _), zero_lt_one, ?_⟩
  intro Q lam h₀ h₁ P K hK hD
  obtain ⟨hD', _hhalf, _htail, hfirst, hcond⟩ := ht Q lam h₀ h₁ P K hK
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  letI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  letI : IsProbabilityMeasure ν := regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hν : (∫⁻ q, regenerationExponentialWeight hd lam l a 1 q.2 ∂ν) ≤
      ENNReal.ofReal (max M 1) := hcond.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hμ : (∫⁻ q, regenerationExponentialWeight hd lam l a 1 q.2 ∂μ) ≤
      ENNReal.ofReal (max M 1) := hfirst.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hfν := regenerationTime_ne_top_ae_of_exponentialMoment hd lam l a 1 ν
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hν)
  have hfμ := regenerationTime_ne_top_ae_of_exponentialMoment hd lam l a 1 μ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hμ)
  have hlpos : 0 < l := hlt.trans_le ((le_max_left _ _).trans hl)
  have hr : r₀ < 2 * l := hrt.trans_le
    (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hl) (by norm_num))
  have hpow (j : ℕ) : (∫⁻ q, regenerationExponentialWeight hd lam l a j q.2 ∂ν) ≤
      ENNReal.ofReal ((max M 1) ^ j) := by
    induction j with
    | zero => simp only [many_cycle_weight_zero, lintegral_one, measure_univ,
        pow_zero, ENNReal.ofReal_one, le_refl]
    | succ j ih =>
      rw [many_cycle_moment_succ hfac hd Q lam h₀ h₁ l δ hlpos hr hδ hδ₁ P K hK hD ν
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr rfl) hfν a j]
      exact (mul_le_mul' hν ih).trans_eq (by
        rw [← ENNReal.ofReal_mul (le_max_of_le_right zero_le_one), pow_succ, mul_comm])
  refine ⟨hpow, ?_⟩
  intro j
  cases j with
  | zero => simp only [many_cycle_weight_zero, lintegral_one, measure_univ,
      pow_zero, mul_one, ENNReal.ofReal_one, le_refl]
  | succ j =>
    rw [many_cycle_moment_succ hfac hd Q lam h₀ h₁ l δ hlpos hr hδ hδ₁ P K hK hD μ
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inl rfl) hfμ a j]
    exact (mul_le_mul' hμ (hpow j)).trans_eq (by
      rw [one_mul, ← ENNReal.ofReal_mul (le_max_of_le_right zero_le_one), pow_succ, mul_comm])

end EinsteinFull.Blueprint
