import EinsteinFull.Blueprint.Foundation.Draft.SbxCFactorizationSmoothR01
import EinsteinFull.Blueprint.G1.Draft.SbxCRenewalSmoothR01
import EinsteinFull.Blueprint.G1.Draft.SbxCRenewalZeroExclusionSmoothR02
import EinsteinFull.Blueprint.G1.Proofs.W1Queue0212_2

/-! Draft smooth-law many-cycle estimates, conditional on their source inputs. -/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint.SbxCManyCycleSmoothR03
open EinsteinRelation Regeneration EinsteinFull.Work.W5

/-- The smooth factorization supplies the actual first-cycle moment recursion. -/
theorem many_cycle_moment_succ_smooth
    (hfac : SbxCFactorizationR01.environmentalFactorizationSmoothStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hr : D.dependenceRange < 2 * l) (hδ : 0 < δ) (hδ₁ : δ < 1)
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
  let : IsProbabilityMeasure ν := regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
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
      have H := (hfac d hd D Q hQ lam h₀ h₁ l δ hl hr hδ hδ₁ P K hK hD).1
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

/-- Smooth many-cycle moments from factorization and first-cycle tails. -/
theorem manyCycleSmooth_of_deps
    (hfac : SbxCFactorizationR01.environmentalFactorizationSmoothStmt)
    (htails : SbxCRenewalZeroExclusionR02.firstCycleTailsSmoothStmt)
    (htransfer : SbxCRenewalR01.couplingParameterTransferSmoothStmt) :
    SbxCRenewalR01.manyCycleSmoothStmt := by
  intro d hd D
  obtain ⟨lt, hlt, hrt, ht⟩ := htails d hd D
  obtain ⟨lp, _hlp, _hrp, _hp⟩ := htransfer d hd D
  refine ⟨max lt lp, hlt.trans_le (le_max_left _ _),
    hrt.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)), ?_⟩
  intro l hl δ hδ hδ₁
  obtain ⟨c, C, a, M, _hc, _hC, ha, _hac, hM, ht⟩ :=
    ht l ((le_max_left _ _).trans hl) δ hδ hδ₁
  refine ⟨a, max M 1, 1, ha, hM.trans_le (le_max_left _ _), zero_lt_one, ?_⟩
  intro Q hQ lam h₀ h₁ P K hK hD
  obtain ⟨hD', _hhalf, _htail, hfirst, hcond⟩ := ht Q hQ lam h₀ h₁ P K hK
  let μ := annealedCoupledLaw Q.measure K
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  let : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let : IsProbabilityMeasure ν := regenerationConditionedLaw_probability hd Q lam l K hK.1 hD
  have hν : (∫⁻ q, regenerationExponentialWeight hd lam l a 1 q.2 ∂ν) ≤
      ENNReal.ofReal (max M 1) := hcond.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hμ : (∫⁻ q, regenerationExponentialWeight hd lam l a 1 q.2 ∂μ) ≤
      ENNReal.ofReal (max M 1) := hfirst.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hfν := regenerationTime_ne_top_ae_of_exponentialMoment hd lam l a 1 ν
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hν)
  have hfμ := regenerationTime_ne_top_ae_of_exponentialMoment hd lam l a 1 μ
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hμ)
  have hlpos : 0 < l := hlt.trans_le ((le_max_left _ _).trans hl)
  have hr : D.dependenceRange < 2 * l := hrt.trans_le
    (mul_le_mul_of_nonneg_left ((le_max_left _ _).trans hl) (by norm_num))
  have hpow (j : ℕ) : (∫⁻ q, regenerationExponentialWeight hd lam l a j q.2 ∂ν) ≤
      ENNReal.ofReal ((max M 1) ^ j) := by
    induction j with
    | zero => simp only [many_cycle_weight_zero, lintegral_one, measure_univ,
        pow_zero, ENNReal.ofReal_one, le_refl]
    | succ j ih =>
      rw [many_cycle_moment_succ_smooth hfac hd D Q hQ lam h₀ h₁ l δ hlpos hr hδ hδ₁ P K hK hD ν
        (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inr rfl) hfν a j]
      exact (mul_le_mul' hν ih).trans_eq (by
        rw [← ENNReal.ofReal_mul (le_max_of_le_right zero_le_one), pow_succ, mul_comm])
  refine ⟨hpow, ?_⟩
  intro j
  cases j with
  | zero => simp only [many_cycle_weight_zero, lintegral_one, measure_univ,
      pow_zero, mul_one, ENNReal.ofReal_one, le_refl]
  | succ j =>
    rw [many_cycle_moment_succ_smooth hfac hd D Q hQ lam h₀ h₁ l δ hlpos hr hδ hδ₁ P K hK hD μ
      (by simp only [Set.mem_insert_iff, Set.mem_singleton_iff]; exact Or.inl rfl) hfμ a j]
    exact (mul_le_mul' hμ (hpow j)).trans_eq (by
      rw [one_mul, ← ENNReal.ofReal_mul (le_max_of_le_right zero_le_one), pow_succ, mul_comm])

end EinsteinFull.Blueprint.SbxCManyCycleSmoothR03
