import EinsteinFull.Regeneration.GMPSplitSourceTransfer
import EinsteinRelation.Regeneration.DeterministicRestartJoint
import Mathlib.Probability.Kernel.MeasurableIntegral

/-!
# The source split coupling's actual one-step joint law

GMP's restart clause concerns the future path conditioned on the current coin.
Together with independence of that coin from the exact finite past, it determines
one joint transition of the past, the shifted path and the current coin. No joint
restart assertion for the entire future coin sequence is assumed here.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration
open EinsteinFull.External.Source.GMP

/-- The source's literal first-coin conditional path law, as a kernel in the
spatial starting point. This uses restriction and normalization of the given
joint path/coin kernel, without choosing a conditional distribution. -/
def sourceConditionalPathKernel {d : ℕ}
    (K : Kernel (Vec d) (CoupledSample d)) (b : Bool) : Kernel (Vec d) (Path d) where
  toFun x := conditionalPathLaw K x b
  measurable' := by
    apply Measure.measurable_of_measurable_coe
    intro A hA
    have hs : MeasurableSet {z : CoupledSample d | z.2 0 = b} :=
      measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd) measurable_const
    have hm := ((K.restrict hs).map Prod.fst).measurable_coe hA
    have h := (K.measurable_coe hs).inv.mul hm
    simp only [Kernel.map_apply _ measurable_fst, Kernel.restrict_apply] at h
    have h2 : Measurable (fun a => ((K a) {z : CoupledSample d | z.2 0 = b})⁻¹ *
        (Measure.map Prod.fst ((K a).restrict {z : CoupledSample d | z.2 0 = b})) A) := h
    have hmap : ∀ (c : ℝ≥0∞) (μ : Measure (CoupledSample d)),
        (c • μ).map Prod.fst = c • μ.map Prod.fst := fun c μ =>
      Measure.map_smul c
        (measurable_fst : Measurable (Prod.fst : CoupledSample d → Path d)).aemeasurable
    have h3 : ∀ a, (conditionalPathLaw K a b) A =
        ((K a) {z : CoupledSample d | z.2 0 = b})⁻¹ *
        (Measure.map Prod.fst ((K a).restrict {z : CoupledSample d | z.2 0 = b})) A := by
      intro a
      simp only [conditionalPathLaw, ProbabilityTheory.cond, hmap, Measure.smul_apply,
        smul_eq_mul]
    have h4 : (fun a => (conditionalPathLaw K a b) A) = fun a => ((K a)
        {z : CoupledSample d | z.2 0 = b})⁻¹ *
        (Measure.map Prod.fst ((K a).restrict {z : CoupledSample d | z.2 0 = b})) A :=
      funext h3
    show Measurable (fun a => (conditionalPathLaw K a b) A)
    rw [h4]
    exact h2

/-- Both literal source conditional path branches are probability measures
when their Bernoulli weights are strictly positive. -/
theorem isMarkovKernel_sourceConditionalPathKernel {d : ℕ}
    {P : Vec d → Measure (Path d)} {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    (K : Kernel (Vec d) (CoupledSample d))
    (hK : IsSourceSplitCoupling P Δ δ R i K)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (b : Bool) :
    IsMarkovKernel (sourceConditionalPathKernel K b) := by
  constructor
  intro x
  letI := (hK x).1
  have hs : K x {z | z.2 0 = b} ≠ 0 := by
    rw [source_split_coin_measure hK]
    cases b
    · exact (ENNReal.ofReal_pos.mpr (sub_pos.mpr hδ₁)).ne'
    · exact (ENNReal.ofReal_pos.mpr hδ₀).ne'
  letI := cond_isProbabilityMeasure hs
  change IsProbabilityMeasure ((cond (K x) {z | z.2 0 = b}).map Prod.fst)
  infer_instance

/-- Averaging any exact-past test against a specified current coin uses the
source's stated future-coin independence and its literal Bernoulli marginal. -/
theorem source_split_coin_test {d : ℕ}
    {P : Vec d → Measure (Path d)} {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    {K : Vec d → Measure (CoupledSample d)}
    (hK : IsSourceSplitCoupling P Δ δ R i K) (x : Vec d) (m : ℕ) (b : Bool)
    (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hδ₀ : 0 ≤ δ) (hδ₁ : δ ≤ 1) :
    (∫ z, H z * (if z.2 m = b then 1 else 0) ∂K x) =
      (if b then δ else 1 - δ) * ∫ z, H z ∂K x := by
  letI := (hK x).1
  let χ : CoupledSample d → ℝ := fun z => if z.2 m = b then 1 else 0
  have hs : MeasurableSet {z : CoupledSample d | z.2 m = b} :=
    measurableSet_eq_fun ((measurable_pi_apply m).comp measurable_snd) measurable_const
  have hχ : Measurable χ := measurable_const.ite hs measurable_const
  have hχfuture : @Measurable (CoupledSample d) ℝ
      (MeasurableSpace.comap
        (fun z : CoupledSample d => fun n : ℕ => z.2 (m + n)) inferInstance)
      inferInstance χ := by
    have hf : @Measurable (CoupledSample d) (ℕ → Bool)
        (MeasurableSpace.comap
          (fun z : CoupledSample d => fun n : ℕ => z.2 (m + n)) inferInstance)
        inferInstance (fun z => fun n : ℕ => z.2 (m + n)) :=
      Measurable.of_comap_le le_rfl
    have hc := (measurable_pi_apply 0).comp hf
    exact measurable_const.ite (measurableSet_eq_fun hc measurable_const) measurable_const
  have hind : IndepFun H χ (K x) :=
    indep_of_indep_of_le_right
      (indep_of_indep_of_le_left ((hK x).2.2.2.1 m).symm hH.comap_le)
      hχfuture.comap_le
  have hχint : (∫ z, χ z ∂K x) = if b then δ else 1 - δ := by
    have heq : χ = Set.indicator {z : CoupledSample d | z.2 m = b} (fun _ => 1) := by
      funext z
      simp only [χ, Set.indicator, Set.mem_setOf_eq]
    rw [heq, integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one,
      measureReal_def, source_split_coin_measure hK, ENNReal.toReal_ofReal]
    cases b <;> simp only [Bool.false_eq_true, ↓reduceIte]
    · exact sub_nonneg.mpr hδ₁
    · exact hδ₀
  change (∫ z, H z * χ z ∂K x) = _
  rw [hind.integral_fun_mul_eq_mul_integral
    (hH.mono (EinsteinRelation.Probability.finiteHistorySigma_le Δ m)
      le_rfl).aestronglyMeasurable hχ.aestronglyMeasurable, hχint, mul_comm]

private theorem bounded_mul {α : Type*} (F G : α → ℝ)
    (hF : BoundedRealTest F) (hG : BoundedRealTest G) :
    BoundedRealTest (fun a => F a * G a) := by
  obtain ⟨C, hC⟩ := hF
  obtain ⟨D, hD⟩ := hG
  refine ⟨|C| * |D|, fun a => ?_⟩
  rw [abs_mul]
  exact mul_le_mul ((hC a).trans (le_abs_self _)) ((hD a).trans (le_abs_self _))
    (abs_nonneg _) (abs_nonneg _)

private theorem bounded_coin_indicator {d : ℕ} (m : ℕ) (b : Bool) :
    BoundedRealTest (fun z : CoupledSample d => if z.2 m = b then (1 : ℝ) else 0) := by
  refine ⟨1, fun z => ?_⟩
  dsimp only
  split <;> norm_num

/-- The current-coin source restart followed by fresh-coin averaging determines
its full future-path transition against every bounded exact-past test. The
future coins are not part of this assertion. -/
theorem source_split_path_coin_test {d : ℕ}
    {P : Vec d → Measure (Path d)} {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    (K : Kernel (Vec d) (CoupledSample d))
    (hK : IsSourceSplitCoupling P Δ δ R i K)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (x : Vec d) (m : ℕ) (b : Bool)
    (H : CoupledSample d → ℝ) (F : Path d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hbH : BoundedRealTest H) (hF : Measurable F) (hbF : BoundedRealTest F) :
    (∫ z, H z * (if z.2 m = b then 1 else 0) *
      F (pathTimeShift z.1 (m * Δ)) ∂K x) =
      ∫ z, H z * ((if b then δ else 1 - δ) *
        ∫ γ, F γ ∂conditionalPathLaw K (z.1 (m * Δ)) b) ∂K x := by
  letI := (hK x).1
  letI := isMarkovKernel_sourceConditionalPathKernel K hK hδ₀ hδ₁ b
  let χ : CoupledSample d → ℝ := fun z => if z.2 m = b then 1 else 0
  let J : Vec d → ℝ := fun y => ∫ γ, F γ ∂sourceConditionalPathKernel K b y
  have hJ : Measurable J := hF.stronglyMeasurable.integral_kernel.measurable
  have hbJ : BoundedRealTest J := by
    obtain ⟨C, hC⟩ := hbF
    refine ⟨C, fun y => ?_⟩
    have h := norm_integral_le_of_norm_le_const (μ := sourceConditionalPathKernel K b y)
      (Filter.Eventually.of_forall fun γ => (show ‖F γ‖ ≤ C by
        simpa only [Real.norm_eq_abs] using hC γ))
    simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using h
  have hX : @Measurable (CoupledSample d) (Vec d)
      (finiteHistorySigma Δ m) inferInstance (fun z => z.1 (m * Δ)) := by
    apply EinsteinRelation.Probability.measurable_of_finite_history_prefix Δ m _
      ((measurable_pathPosition _).comp measurable_fst)
    intro z z' hp _
    exact hp _ ⟨bot_le, le_rfl⟩
  have hχ : @Measurable (CoupledSample d) ℝ
      (currentCoinHistory Δ m) inferInstance χ := by
    have hc : @Measurable (CoupledSample d) Bool
        (currentCoinHistory Δ m) inferInstance (fun z => z.2 m) :=
      Measurable.of_comap_le le_sup_right
    exact measurable_const.ite (measurableSet_eq_fun hc measurable_const) measurable_const
  have hbχ := bounded_coin_indicator (d := d) m b
  have hr := ((hK x).2.2.2.2.1 m (fun z => H z * χ z) F
    ((hH.mono le_sup_left le_rfl).mul hχ) (bounded_mul H χ hbH hbχ) hF hbF).2
  have heq (z : CoupledSample d) :
      H z * χ z * (∫ γ, F γ ∂conditionalPathLaw K (z.1 (m * Δ)) (z.2 m)) =
        (H z * J (z.1 (m * Δ))) * χ z := by
    by_cases hz : z.2 m = b
    · simp only [χ, hz, ↓reduceIte, mul_one]
      rfl
    · simp only [χ, hz, ↓reduceIte, mul_zero, zero_mul]
  calc
    _ = ∫ z, (H z * J (z.1 (m * Δ))) * χ z ∂K x :=
      hr.trans (integral_congr_ae (Filter.Eventually.of_forall heq))
    _ = (if b then δ else 1 - δ) * ∫ z, H z * J (z.1 (m * Δ)) ∂K x :=
      source_split_coin_test hK x m b _ (hH.mul (hJ.comp hX)) hδ₀.le hδ₁.le
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        change (if b then δ else 1 - δ) * (H z * J (z.1 (m * Δ))) =
          H z * ((if b then δ else 1 - δ) * J (z.1 (m * Δ)))
        ring

private theorem first_coin_integral {d : ℕ}
    {P : Vec d → Measure (Path d)} {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    {K : Vec d → Measure (CoupledSample d)}
    (hK : IsSourceSplitCoupling P Δ δ R i K)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (x : Vec d) (b : Bool)
    (F : Path d → ℝ) (hF : Measurable F) :
    (∫ z, (if z.2 0 = b then 1 else 0) * F z.1 ∂K x) =
      (if b then δ else 1 - δ) * ∫ γ, F γ ∂conditionalPathLaw K x b := by
  have hs : MeasurableSet {z : CoupledSample d | z.2 0 = b} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd) measurable_const
  have hw : 0 < (if b then δ else 1 - δ) := by
    cases b
    · exact sub_pos.mpr hδ₁
    · exact hδ₀
  rw [conditionalPathLaw,
    integral_map measurable_fst.aemeasurable hF.aestronglyMeasurable,
    ProbabilityTheory.cond, integral_smul_measure, source_split_coin_measure hK,
    ENNReal.toReal_inv, ENNReal.toReal_ofReal hw.le, smul_eq_mul,
    ← mul_assoc, mul_inv_cancel₀ hw.ne', one_mul]
  rw [← integral_indicator hs]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    by_cases hz : z.2 0 = b <;> simp [hz]

/-- The literal first path/coin projection of the supplied source kernel. -/
def sourceFirstPathCoinKernel {d : ℕ} (K : Kernel (Vec d) (CoupledSample d)) :
    Kernel (Vec d) (Path d × Bool) :=
  K.map (fun z => (z.1, z.2 0))

/-- Its two-branch integral is the conditional path law with exactly the
source Bernoulli weights. No independent path and coin marginal is substituted. -/
theorem integral_sourceFirstPathCoinKernel {d : ℕ}
    {P : Vec d → Measure (Path d)} {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    (K : Kernel (Vec d) (CoupledSample d))
    (hK : IsSourceSplitCoupling P Δ δ R i K)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (x : Vec d)
    (Φ : Path d × Bool → ℝ) (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ q, Φ q ∂sourceFirstPathCoinKernel K x) =
      δ * (∫ γ, Φ (γ, true) ∂conditionalPathLaw K x true) +
      (1 - δ) * (∫ γ, Φ (γ, false) ∂conditionalPathLaw K x false) := by
  letI := (hK x).1
  have hm (b : Bool) : Measurable (fun z : CoupledSample d =>
      (if z.2 0 = b then (1 : ℝ) else 0) * Φ (z.1, b)) := by
    exact (measurable_const.ite
      (measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd)
        measurable_const) measurable_const).mul
      (hΦ.comp (measurable_fst.prodMk measurable_const))
  have hb (b : Bool) : BoundedRealTest (fun z : CoupledSample d =>
      (if z.2 0 = b then (1 : ℝ) else 0) * Φ (z.1, b)) :=
    bounded_mul _ _ (bounded_coin_indicator 0 b)
      (by obtain ⟨C, hC⟩ := hbΦ; exact ⟨C, fun z => hC (z.1, b)⟩)
  have hi (b : Bool) : Integrable (fun z : CoupledSample d =>
      (if z.2 0 = b then (1 : ℝ) else 0) * Φ (z.1, b)) (K x) := by
    obtain ⟨C, hC⟩ := hb b
    exact Integrable.of_bound (hm b).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)
  rw [sourceFirstPathCoinKernel, Kernel.map_apply _ (by fun_prop),
    integral_map (by fun_prop) hΦ.aestronglyMeasurable]
  calc
    _ = ∫ z, ((if z.2 0 = true then 1 else 0) * Φ (z.1, true) +
        (if z.2 0 = false then 1 else 0) * Φ (z.1, false)) ∂K x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by cases hcoin : z.2 0 <;> simp [hcoin]
    _ = _ := by
      rw [integral_add (hi true) (hi false),
        first_coin_integral hK hδ₀ hδ₁ x true (fun γ => Φ (γ, true))
          (hΦ.comp (measurable_id.prodMk measurable_const)),
        first_coin_integral hK hδ₀ hδ₁ x false (fun γ => Φ (γ, false))
          (hΦ.comp (measurable_id.prodMk measurable_const))]
      rfl

/-- The source's current-coin path restart implies the joint transition test
for the shifted path and that coin. The initial joint law retains their actual
correlation, and only the source's stated restart and independence are used. -/
theorem source_split_path_coin_restart {d : ℕ}
    {P : Vec d → Measure (Path d)} {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    (K : Kernel (Vec d) (CoupledSample d))
    (hK : IsSourceSplitCoupling P Δ δ R i K)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (x : Vec d) (m : ℕ)
    (H : CoupledSample d → ℝ) (Φ : Path d × Bool → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hbH : BoundedRealTest H) (hΦ : Measurable Φ) (hbΦ : BoundedRealTest Φ) :
    (∫ z, H z * Φ (pathTimeShift z.1 (m * Δ), z.2 m) ∂K x) =
      ∫ z, H z * (∫ q, Φ q ∂sourceFirstPathCoinKernel K (z.1 (m * Δ))) ∂K x := by
  letI := (hK x).1
  let J : Bool → Vec d → ℝ := fun b y =>
    (if b then δ else 1 - δ) * ∫ γ, Φ (γ, b) ∂sourceConditionalPathKernel K b y
  have hJ (b : Bool) : Measurable (J b) :=
    measurable_const.mul (hΦ.comp (measurable_id.prodMk measurable_const)).stronglyMeasurable.integral_kernel.measurable
  have hbJ (b : Bool) : BoundedRealTest (J b) := by
    letI := isMarkovKernel_sourceConditionalPathKernel K hK hδ₀ hδ₁ b
    obtain ⟨C, hC⟩ := hbΦ
    refine ⟨|if b then δ else 1 - δ| * |C|, fun y => ?_⟩
    rw [abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    have h := norm_integral_le_of_norm_le_const (μ := sourceConditionalPathKernel K b y)
      (Filter.Eventually.of_forall fun γ => (show ‖Φ (γ, b)‖ ≤ C by
        simpa only [Real.norm_eq_abs] using hC (γ, b)))
    have hbound : |∫ γ, Φ (γ, b) ∂sourceConditionalPathKernel K b y| ≤ C := by
      simpa only [probReal_univ, mul_one, Real.norm_eq_abs] using h
    exact hbound.trans (le_abs_self C)
  have hHfull := hH.mono (EinsteinRelation.Probability.finiteHistorySigma_le Δ m) le_rfl
  have hshift : Measurable (fun z : CoupledSample d => pathTimeShift z.1 (m * Δ)) :=
    ((measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_id)).fst
  have hi (b : Bool) : Integrable (fun z : CoupledSample d => H z *
      (if z.2 m = b then 1 else 0) * Φ (pathTimeShift z.1 (m * Δ), b)) (K x) := by
    have hm : Measurable (fun z : CoupledSample d => H z *
        (if z.2 m = b then (1 : ℝ) else 0) * Φ (pathTimeShift z.1 (m * Δ), b)) :=
      (hHfull.mul (measurable_const.ite
      (measurableSet_eq_fun ((measurable_pi_apply m).comp measurable_snd)
        measurable_const) measurable_const)).mul
      (hΦ.comp (hshift.prodMk measurable_const))
    obtain ⟨C, hC⟩ := bounded_mul _ _
      (bounded_mul _ _ hbH (bounded_coin_indicator m b))
      (show BoundedRealTest (fun z : CoupledSample d =>
        Φ (pathTimeShift z.1 (m * Δ), b)) from by
          obtain ⟨C, hC⟩ := hbΦ; exact ⟨C, fun z => hC _⟩)
    exact Integrable.of_bound hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)
  have hiJ (b : Bool) : Integrable (fun z : CoupledSample d =>
      H z * J b (z.1 (m * Δ))) (K x) := by
    have hm : Measurable (fun z : CoupledSample d => H z * J b (z.1 (m * Δ))) :=
      hHfull.mul ((hJ b).comp ((measurable_pathPosition _).comp measurable_fst))
    obtain ⟨C, hC⟩ := bounded_mul H (fun z => J b (z.1 (m * Δ))) hbH
      (by obtain ⟨C, hC⟩ := hbJ b; exact ⟨C, fun z => hC _⟩)
    exact Integrable.of_bound hm.aestronglyMeasurable C
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hC z)
  calc
    _ = ∫ z, (H z * (if z.2 m = true then 1 else 0) *
        Φ (pathTimeShift z.1 (m * Δ), true) +
        H z * (if z.2 m = false then 1 else 0) *
        Φ (pathTimeShift z.1 (m * Δ), false)) ∂K x := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by cases hc : z.2 m <;> simp [hc]
    _ = (∫ z, H z * J true (z.1 (m * Δ)) ∂K x) +
        ∫ z, H z * J false (z.1 (m * Δ)) ∂K x := by
      rw [integral_add (hi true) (hi false),
        source_split_path_coin_test K hK hδ₀ hδ₁ x m true H
          (fun γ => Φ (γ, true)) hH hbH
          (hΦ.comp (measurable_id.prodMk measurable_const))
          (by obtain ⟨C, hC⟩ := hbΦ; exact ⟨C, fun γ => hC _⟩),
        source_split_path_coin_test K hK hδ₀ hδ₁ x m false H
          (fun γ => Φ (γ, false)) hH hbH
          (hΦ.comp (measurable_id.prodMk measurable_const))
          (by obtain ⟨C, hC⟩ := hbΦ; exact ⟨C, fun γ => hC _⟩)]
      rfl
    _ = ∫ z, H z * (J true (z.1 (m * Δ)) + J false (z.1 (m * Δ))) ∂K x := by
      rw [← integral_add (hiJ true) (hiJ false)]
      simp only [mul_add]
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun z => by
        dsimp only
        rw [integral_sourceFirstPathCoinKernel K hK hδ₀ hδ₁ _ Φ hΦ hbΦ]
        rfl

/-- The actual source joint law of the stopped exact past, shifted whole path
and current coin. This is the one-step law needed to iterate finite histories;
it includes no additional restart premise for the future coin sequence. -/
theorem source_split_past_path_coin_joint {d : ℕ}
    {P : Vec d → Measure (Path d)} {Δ : ℝ≥0} {δ R : ℝ} {i : Fin d}
    (K : Kernel (Vec d) (CoupledSample d)) [IsMarkovKernel K]
    (hK : IsSourceSplitCoupling P Δ δ R i K)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (x : Vec d) (m : ℕ) :
    (K x).map (fun z => (EinsteinRelation.Probability.stoppedHistorySample Δ m z,
      (pathTimeShift z.1 (m * Δ), z.2 m))) =
      ((K x).compProd ((sourceFirstPathCoinKernel K).comap
        (fun z => z.1 (m * Δ)) ((measurable_pathPosition _).comp measurable_fst))).map
          (fun q => (EinsteinRelation.Probability.stoppedHistorySample Δ m q.1, q.2)) := by
  letI : IsMarkovKernel (sourceFirstPathCoinKernel K) :=
    Kernel.IsMarkovKernel.map K (by fun_prop)
  have hstop := EinsteinRelation.Probability.measurable_stoppedHistorySample (d := d) Δ m
  have hstopfull := hstop.mono (EinsteinRelation.Probability.finiteHistorySigma_le Δ m) le_rfl
  have hshift : Measurable (fun z : CoupledSample d => pathTimeShift z.1 (m * Δ)) :=
    ((measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_id)).fst
  have hpos : Measurable (fun z : CoupledSample d => z.1 (m * Δ)) :=
    (measurable_pathPosition _).comp measurable_fst
  haveI : IsFiniteKernel ((sourceFirstPathCoinKernel K).comap
      (fun z : CoupledSample d => z.1 (m * Δ)) hpos) :=
    ProbabilityTheory.Kernel.IsFiniteKernel.comap (sourceFirstPathCoinKernel K) hpos
  apply map_pair_eq_restart_of_product_tests (K x) _ _ hstopfull
    (hshift.prodMk ((measurable_pi_apply m).comp measurable_snd))
  intro H Φ hH hbH hΦ hbΦ
  exact source_split_path_coin_restart K hK hδ₀ hδ₁ x m
    (fun z => H (EinsteinRelation.Probability.stoppedHistorySample Δ m z)) Φ
    (hH.comp hstop) (by obtain ⟨C, hC⟩ := hbH; exact ⟨C, fun z => hC _⟩) hΦ hbΦ

end EinsteinFull.Regeneration
