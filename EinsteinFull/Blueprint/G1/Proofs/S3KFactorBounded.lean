import EinsteinFull.Blueprint.G1.Proofs.S3KFactorSlice

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime couplingRegion)

/-! # `rt:k-factor`: bounded factorization under both laws, and truncation -/

theorem integral_cond_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (f : α → ℝ) :
    (∫ x, f x ∂ProbabilityTheory.cond μ s) = ((μ s).toReal)⁻¹ * ∫ x in s, f x ∂μ := by
  unfold ProbabilityTheory.cond
  rw [integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]

theorem setIntegral_cond_eq {α : Type*} [MeasurableSpace α] (μ : Measure α) (s t : Set α)
    (ht : MeasurableSet t) (f : α → ℝ) :
    (∫ x in t, f x ∂ProbabilityTheory.cond μ s) =
      ((μ s).toReal)⁻¹ * ∫ x in t ∩ s, f x ∂μ := by
  unfold ProbabilityTheory.cond
  rw [Measure.restrict_smul, integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul,
    Measure.restrict_restrict ht]

theorem integrable_cond {α : Type*} [MeasurableSpace α] (μ : Measure α) (s : Set α)
    (hs : μ s ≠ 0) (f : α → ℝ) (hf : Integrable f μ) :
    Integrable f (ProbabilityTheory.cond μ s) := by
  unfold ProbabilityTheory.cond
  exact (hf.restrict).smul_measure (ENNReal.inv_ne_top.mpr hs)

theorem abs_clip_le (x N : ℝ) (hN : 0 ≤ N) : |max (-N) (min x N)| ≤ |x| := by
  rcases le_total x (-N) with h1 | h1
  · have hmin : min x N = x := min_eq_left (h1.trans (by linarith))
    rw [hmin, max_eq_left h1, abs_neg, abs_of_nonneg hN,
      abs_of_nonpos (h1.trans (by linarith))]
    linarith
  · rcases le_total x N with h2 | h2
    · rw [min_eq_left h2, max_eq_right h1]
    · rw [min_eq_right h2, max_eq_right (by linarith), abs_of_nonneg hN,
        abs_of_nonneg (hN.trans h2)]
      exact h2

theorem tendsto_clip (x : ℝ) :
    Filter.Tendsto (fun N : ℕ => max (-(N : ℝ)) (min x N)) Filter.atTop (nhds x) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [Filter.eventually_ge_atTop ⌈|x|⌉₊] with N hN
  have h : |x| ≤ N := (Nat.le_ceil _).trans (by exact_mod_cast hN)
  have h' := abs_le.mp h
  rw [min_eq_left h'.2, max_eq_right (by linarith [h'.1])]

theorem limit_factor {α : Type*} [MeasurableSpace α] (ρ : Measure α) (s : Set α) (c : ℝ)
    (f : α → ℝ) (fc : ℕ → α → ℝ) (g : α → ℝ) (M : ℝ)
    (hfm : ∀ N, Measurable (fc N)) (hg : Measurable g) (hgM : ∀ x, |g x| ≤ M)
    (hbound : ∀ N x, |fc N x| ≤ |f x|)
    (hlim : ∀ x, Filter.Tendsto (fun N => fc N x) Filter.atTop (nhds (f x)))
    (hint : Integrable f (ρ.restrict s))
    (h : ∀ N, (∫ x in s, fc N x * g x ∂ρ) = c * ∫ x in s, fc N x ∂ρ) :
    (∫ x in s, f x * g x ∂ρ) = c * ∫ x in s, f x ∂ρ := by
  have t1 : Filter.Tendsto (fun N => ∫ x in s, fc N x * g x ∂ρ) Filter.atTop
      (nhds (∫ x in s, f x * g x ∂ρ)) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖f x‖ * M)
      (fun N => ((hfm N).mul hg).aestronglyMeasurable) (hint.norm.mul_const M)
      (fun N => ae_of_all _ fun x => ?_) (ae_of_all _ fun x => (hlim x).mul_const (g x))
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_mul (hbound N x) (hgM x) (abs_nonneg _) (abs_nonneg _)
  have t2 : Filter.Tendsto (fun N => c * ∫ x in s, fc N x ∂ρ) Filter.atTop
      (nhds (c * ∫ x in s, f x ∂ρ)) := by
    refine Filter.Tendsto.const_mul c (tendsto_integral_of_dominated_convergence
      (fun x => ‖f x‖) (fun N => (hfm N).aestronglyMeasurable) hint.norm
      (fun N => ae_of_all _ fun x => ?_) (ae_of_all _ hlim))
    rw [Real.norm_eq_abs, Real.norm_eq_abs]
    exact hbound N x
  have hfun : (fun N => ∫ x in s, fc N x * g x ∂ρ) = fun N => c * ∫ x in s, fc N x ∂ρ :=
    funext h
  rw [hfun] at t1
  exact tendsto_nhds_unique t1 t2

theorem integrable_fst_annealed {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Regeneration.CoupledQuenchedLaws d) (f : FieldPair d → ℝ) (hf : Measurable f)
    (hint : Integrable f Q.measure) :
    Integrable (fun q : FieldPair d × CoupledSample d => f q.1)
      (Regeneration.annealedCoupledLaw Q.measure K) := by
  refine ⟨(hf.comp measurable_fst).aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral Regeneration.annealedCoupledLaw
  have hm : Measurable (fun q : FieldPair d × CoupledSample d => ‖f q.1‖ₑ) :=
    (hf.comp measurable_fst).enorm
  rw [Measure.lintegral_compProd hm]
  calc ∫⁻ ω, ∫⁻ z, ‖f ω‖ₑ ∂(Probability.probabilityPart (Regeneration.originCoupledLaw K)) ω
        ∂Q.measure
      = ∫⁻ ω, ‖f ω‖ₑ * (Probability.probabilityPart (Regeneration.originCoupledLaw K)) ω
          Set.univ ∂Q.measure := by simp [lintegral_const]
    _ ≤ ∫⁻ ω, ‖f ω‖ₑ ∂Q.measure := by
      apply lintegral_mono
      intro ω
      refine mul_le_of_le_one_right' ?_
      rw [Probability.probabilityPart_apply]
      split_ifs with h
      · exact h.le
      · simp
    _ < ∞ := hint.2

/-! ## Bounded factorization -/

open scoped Classical in
theorem bounded_factor_mu {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    (hprebridge : node_rt_u3A_prebridge_u2D_kStmt)
    (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (F : FieldPair d → ℝ)
    (hFloc : Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
      (10 * (k : ℝ) - 4) * (l / lam)}] F)
    (hbF : Regeneration.BoundedRealTest F)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    (∫ q in {q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * Φ (regenerationRecord hd lam l k q) ∂Regeneration.annealedCoupledLaw Q.measure K) =
      (∫ q, Φ (regenerationRecord hd lam l 0 q) ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) *
      ∫ q in {q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 ∂Regeneration.annealedCoupledLaw Q.measure K := by
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  haveI hμprob : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let D := regenerationNoReturn hd (l / lam)
  let slice : Set (FieldPair d × CoupledSample d) := {q | regenerationTime hd lam l k q.2 =
    (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hs : MeasurableSet slice :=
    measurableSet_eq_fun
      ((Regeneration.measurable_regenerationTime (Regeneration.Renewal.regenDelta lam) lam
        (l / lam) (Regeneration.Renewal.forceCoord hd) k).comp measurable_snd)
      measurable_const
  let Φ1 : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ :=
    fun _ => 1
  have hcore := slice_k_factor_core hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast
    hindep hprebridge k n hk hn false F hFloc hbF Φ hΦ hbΦ
  have hcore1 := slice_k_factor_core hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast
    hindep hprebridge k n hk hn false F hFloc hbF Φ1 measurable_const ⟨1, fun _ => by norm_num⟩
  have hpre := (hprebridge d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK k n hk hn).2
  have hGk : ∀ᵐ q ∂μ, q ∈ slice →
      Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n false q.2 = 1 := by
    filter_upwards [hpre] with q hq hmem
    have hΓ := (hq.1.mp hmem).1
    have hmemG : q.2 ∈ GsetK (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n false :=
      ⟨hΓ, fun h => absurd h (by simp)⟩
    simp only [Gk, Set.indicator_of_mem hmemG]
  have e1 : (∫ q in slice, F q.1 * Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) k n false q.2 *
      Φ (regenerationRecord hd lam l k q) ∂μ) =
      ∫ q in slice, F q.1 * Φ (regenerationRecord hd lam l k q) ∂μ := by
    apply setIntegral_congr_ae hs
    filter_upwards [hGk] with q hq hmem
    rw [hq hmem, mul_one]
  have e2 : (∫ q in slice, F q.1 * Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) k n false q.2 *
      Φ1 (regenerationRecord hd lam l k q) ∂μ) = ∫ q in slice, F q.1 ∂μ := by
    apply setIntegral_congr_ae hs
    filter_upwards [hGk] with q hq hmem
    simp only [Φ1, hq hmem, mul_one]
  have hc1 : (∫ q in D, Φ1 (regenerationRecord hd lam l 0 q) ∂μ) = (μ D).toReal := by
    simp [Φ1, measureReal_def]
  have hμD : 0 < (μ D).toReal := ENNReal.toReal_pos hD (measure_ne_top _ _)
  rw [e1] at hcore
  rw [e2, hc1] at hcore1
  change (∫ q in slice, F q.1 * Φ (regenerationRecord hd lam l k q) ∂μ) =
    (∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ProbabilityTheory.cond μ D) *
      ∫ q in slice, F q.1 ∂μ
  rw [integral_cond_eq, hcore, hcore1]
  have := hμD.ne'
  field_simp
  try ring

open scoped Classical in
theorem bounded_factor_nu {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hgeom : node_rt_u3A_global_u2D_geometryStmt)
    (hpast : node_app_u3A_factorization_u23_past_u2D_kernelStmt)
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    (hprebridge : node_rt_u3A_prebridge_u2D_kStmt)
    (k n : ℕ) (hk : 1 ≤ k) (hn : 2 * k ≤ n)
    (F : FieldPair d → ℝ)
    (hFloc : Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
      (10 * (k : ℝ) - 4) * (l / lam)}] F)
    (hbF : Regeneration.BoundedRealTest F)
    (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ)
    (hΦ : Measurable Φ) (hbΦ : Regeneration.BoundedRealTest Φ) :
    (∫ q in {q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
      F q.1 * Φ (regenerationRecord hd lam l k q) ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) =
      (∫ q, Φ (regenerationRecord hd lam l 0 q) ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) *
      ∫ q in {q : FieldPair d × CoupledSample d | regenerationTime hd lam l k q.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F q.1 ∂regenerationConditionedLaw hd Q lam l K hK.1 hD := by
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  haveI hμprob : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let D := regenerationNoReturn hd (l / lam)
  have hDm : MeasurableSet D :=
    (Regeneration.measurableSet_NoBacktracking (l / lam) (Regeneration.Renewal.forceCoord hd)).preimage
      measurable_snd.fst
  let slice : Set (FieldPair d × CoupledSample d) := {q | regenerationTime hd lam l k q.2 =
    (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hs : MeasurableSet slice :=
    measurableSet_eq_fun
      ((Regeneration.measurable_regenerationTime (Regeneration.Renewal.regenDelta lam) lam
        (l / lam) (Regeneration.Renewal.forceCoord hd) k).comp measurable_snd)
      measurable_const
  let Φ1 : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ :=
    fun _ => 1
  have hcore := slice_k_factor_core hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast
    hindep hprebridge k n hk hn true F hFloc hbF Φ hΦ hbΦ
  have hcore1 := slice_k_factor_core hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD hgeom hpast
    hindep hprebridge k n hk hn true F hFloc hbF Φ1 measurable_const ⟨1, fun _ => by norm_num⟩
  have hpre := (hprebridge d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK k n hk hn).2
  have hnr := ae_noReturn_iff_surv hd Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hgeom hprebridge
    k n hk hn
  have hind : ∀ Φ' : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd)
      (l / lam) → ℝ, (∫ q in slice ∩ D, F q.1 * Φ' (regenerationRecord hd lam l k q) ∂μ) =
      ∫ q in slice, F q.1 * Gk (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n true q.2 *
        Φ' (regenerationRecord hd lam l k q) ∂μ := by
    intro Φ'
    rw [← setIntegral_indicator hDm]
    apply setIntegral_congr_ae hs
    filter_upwards [hpre, hnr] with q hq hq2 hmem
    have hΓ := (hq.1.mp hmem).1
    by_cases hqD : q ∈ D
    · have hsurv := (hq2 hmem).mp hqD
      have hmemG : q.2 ∈ GsetK (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) k n true := ⟨hΓ, fun _ => hsurv⟩
      rw [Set.indicator_of_mem hqD]
      simp only [Gk, Set.indicator_of_mem hmemG, mul_one]
    · have hnotG : q.2 ∉ GsetK (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) k n true :=
        fun h => hqD ((hq2 hmem).mpr (h.2 rfl))
      rw [Set.indicator_of_notMem hqD]
      simp only [Gk, Set.indicator_of_notMem hnotG, mul_zero, zero_mul]
  have hind1 : (∫ q in slice ∩ D, F q.1 ∂μ) = ∫ q in slice, F q.1 * Gk
      (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        (Regeneration.Renewal.forceCoord hd) k n true q.2 * Φ1 (regenerationRecord hd lam l k q) ∂μ := by
    rw [← hind Φ1]
    simp [Φ1]
  have hc1 : (∫ q in D, Φ1 (regenerationRecord hd lam l 0 q) ∂μ) = (μ D).toReal := by
    simp [Φ1, measureReal_def]
  have hμD : 0 < (μ D).toReal := ENNReal.toReal_pos hD (measure_ne_top _ _)
  rw [← hind] at hcore
  rw [← hind1, hc1] at hcore1
  change (∫ q in slice, F q.1 * Φ (regenerationRecord hd lam l k q)
      ∂ProbabilityTheory.cond μ D) =
    (∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ProbabilityTheory.cond μ D) *
      ∫ q in slice, F q.1 ∂ProbabilityTheory.cond μ D
  rw [setIntegral_cond_eq μ D slice hs, setIntegral_cond_eq μ D slice hs, integral_cond_eq,
    hcore, hcore1]
  have := hμD.ne'
  field_simp
  try ring

end EinsteinFull.Blueprint
