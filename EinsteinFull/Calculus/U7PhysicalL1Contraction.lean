import EinsteinFull.Calculus.C8FoundationGMPAssociation

open MeasureTheory
open scoped ENNReal NNReal Topology
open EinsteinRelation EinsteinRelation.External.GantertSection7Support

noncomputable section
namespace EinsteinFull

/-- The actual physical evolution is monotone on its L² space. -/
theorem u7_physical_semigroup_mono {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    {f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)} (hfg : f ≤ g) :
    Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f ≤
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t g := by
  apply sub_nonneg.mp
  rw [← map_sub]
  apply (Lp.coeFn_nonneg _).mp
  exact Blueprint.gmpPhysicalSemigroup_positive hd ω lam Λ hΛ hω t
    ((Lp.coeFn_nonneg _).mpr (sub_nonneg.mpr hfg))

/-- Positivity controls the absolute value of the evolution by evolution of the absolute value. -/
theorem u7_physical_semigroup_abs_le {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    |Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f| ≤
      Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t |f| := by
  apply abs_le'.mpr
  constructor
  · exact u7_physical_semigroup_mono hd ω lam Λ hΛ hω t (le_abs_self f)
  · have h := u7_physical_semigroup_mono hd ω lam Λ hΛ hω t (neg_le_abs f)
    simpa only [map_neg] using h

/-- Finite-measure cutoffs of the positive evolution have uniformly bounded mass. -/
theorem u7_physical_positive_cutoff_integral {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (g : Vec d → ℝ) (hg : Integrable g (physicalReversibleMeasure ω hd lam))
    (hg2 : MemLp g 2 (physicalReversibleMeasure ω hd lam))
    (hg0 : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] g)
    (s : Set (Vec d)) (hs : MeasurableSet s)
    (hμs : physicalReversibleMeasure ω hd lam s ≠ ∞) :
    (∫ x in s, Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hg2.toLp g) x
      ∂physicalReversibleMeasure ω hd lam) ≤ ∫ x, g x ∂physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  let q : Lp ℝ 2 μ := indicatorConstLp 2 hs hμs 1
  let P := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
  have hq : ∀ᵐ x ∂μ, 0 ≤ q x ∧ q x ≤ 1 := by
    filter_upwards [indicatorConstLp_coeFn (p := 2) (hs := hs) (hμs := hμs) (c := (1 : ℝ))] with x hx
    rw [hx]
    by_cases hx : x ∈ s <;> simp [hx]
  have hPq := Blueprint.gmpPhysicalSemigroup_submarkov hd ω lam Λ hΛ hω t
    (hq.mono fun _ h => h.1) (hq.mono fun _ h => h.2)
  have hi : Integrable (fun x => (P q) x * g x) μ := by
    apply Integrable.congr (L2.integrable_inner (𝕜 := ℝ) (P q) (hg2.toLp g))
    filter_upwards [hg2.coeFn_toLp] with x hx
    simp only [Real.inner_apply, hx]
  have hle : (∫ x, (P q) x * g x ∂μ) ≤ ∫ x, g x ∂μ := by
    apply integral_mono_ae hi hg
    filter_upwards [hPq, hg0] with x hp hgx
    nlinarith [mul_nonneg (sub_nonneg.mpr hp.2) hgx]
  calc
    _ = inner ℝ q (P (hg2.toLp g)) := (L2.inner_indicatorConstLp_one hs hμs _).symm
    _ = inner ℝ (P q) (hg2.toLp g) :=
      (Blueprint.gmpPhysicalSemigroup_inner_comm hd ω lam Λ hΛ hω t q (hg2.toLp g)).symm
    _ = ∫ x, (P q) x * g x ∂μ := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hg2.coeFn_toLp] with x hx
      simp only [Real.inner_apply, hx]
    _ ≤ _ := hle

/-- The positive physical evolution is integrable and does not increase mass. -/
theorem u7_physical_positive_L1_contraction {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (g : Vec d → ℝ) (hg : Integrable g (physicalReversibleMeasure ω hd lam))
    (hg2 : MemLp g 2 (physicalReversibleMeasure ω hd lam))
    (hg0 : 0 ≤ᵐ[physicalReversibleMeasure ω hd lam] g) :
    Integrable (fun x => Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hg2.toLp g) x)
      (physicalReversibleMeasure ω hd lam) ∧
    (∫ x, Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hg2.toLp g) x
      ∂physicalReversibleMeasure ω hd lam) ≤ ∫ x, g x ∂physicalReversibleMeasure ω hd lam := by
  let μ := physicalReversibleMeasure ω hd lam
  letI : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  let F := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (hg2.toLp g)
  let B : ℕ → Set (Vec d) := fun n => Metric.closedBall 0 n
  have hcover : AECover μ Filter.atTop B := aecover_closedBall tendsto_natCast_atTop_atTop
  have hB (n : ℕ) : μ (B n) ≠ ∞ := (isCompact_closedBall 0 (n : ℝ)).measure_lt_top.ne
  have hpos : 0 ≤ᵐ[μ] F := Blueprint.gmpPhysicalSemigroup_positive hd ω lam Λ hΛ hω t
    (by filter_upwards [hg0, hg2.coeFn_toLp] with x hx he; simpa [he] using hx)
  have hlocal (n : ℕ) : IntegrableOn F (B n) μ :=
    integrableOn_Lp_of_measure_ne_top F (by norm_num) (hB n)
  have hbound (n : ℕ) : (∫ x in B n, F x ∂μ) ≤ ∫ x, g x ∂μ :=
    u7_physical_positive_cutoff_integral hd ω lam Λ hΛ hω t g hg hg2 hg0 (B n)
      Metric.isClosed_closedBall.measurableSet (hB n)
  have hInt : Integrable F μ := hcover.integrable_of_integral_bounded_of_nonneg_ae
    (∫ x, g x ∂μ) hlocal hpos (Filter.Eventually.of_forall hbound)
  exact ⟨hInt, le_of_tendsto (hcover.integral_tendsto_of_countably_generated hInt)
    (Filter.Eventually.of_forall hbound)⟩

/-- The actual unforced physical semigroup contracts the weighted L¹ norm. -/
theorem u7_unforced_physical_L1_contraction
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (g : Vec d → ℝ) (hg1 : Integrable g (physicalReversibleMeasure ω hd 0))
    (hg2 : MemLp g 2 (physicalReversibleMeasure ω hd 0)) :
    Integrable (fun x => Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t
      (hg2.toLp g) x) (physicalReversibleMeasure ω hd 0) ∧
    (∫ x, |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (hg2.toLp g) x|
      ∂physicalReversibleMeasure ω hd 0) ≤
      ∫ x, |g x| ∂physicalReversibleMeasure ω hd 0 := by
  let μ := physicalReversibleMeasure ω hd 0
  let P := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t
  let F := hg2.toLp g
  have hga : MemLp (fun x => |g x|) 2 μ := hg2.abs
  have heq : hga.toLp (fun x => |g x|) = |F| := by
    apply Lp.ext
    filter_upwards [hga.coeFn_toLp, Lp.coeFn_abs F, hg2.coeFn_toLp] with x ha hb hc
    change F x = g x at hc
    rw [ha, hb, hc]
  have hpositive := u7_physical_positive_L1_contraction hd ω 0 Λ hΛ hω t
    (fun x => |g x|) hg1.abs hga (Filter.Eventually.of_forall fun x => abs_nonneg _)
  rw [heq] at hpositive
  have hdom : ∀ᵐ x ∂μ, |(P F) x| ≤ (P |F|) x := by
    have h := (Lp.coeFn_le _ _).mpr (u7_physical_semigroup_abs_le hd ω 0 Λ hΛ hω t F)
    filter_upwards [h, Lp.coeFn_abs (P F)] with x hx he
    change (|P F|) x ≤ (P |F|) x at hx
    simpa only [he] using hx
  have hInt : Integrable (P F) μ := hpositive.1.mono' (Lp.aestronglyMeasurable _)
    (by filter_upwards [hdom] with x hx; simpa only [Real.norm_eq_abs] using hx)
  refine ⟨hInt, ?_⟩
  exact (integral_mono_ae hInt.abs hpositive.1 hdom).trans hpositive.2

#print axioms u7_unforced_physical_L1_contraction

/-- Transport a contraction semigroup across a linear isometry. -/
noncomputable def u7ConjugatedSemigroup {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (U : E ≃ₗᵢ[ℝ] F) : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup F where
  operator t := U.toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((T t).comp U.symm.toContinuousLinearEquiv.toContinuousLinearMap)
  operator_zero := by ext x; simp
  operator_add s t := by ext x; simp [T.add_apply]
  opNorm_le_one t := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖U (T t (U.symm x))‖ ≤ 1 * ‖x‖
    simpa only [U.norm_map, U.symm.norm_map, one_mul] using T.norm_apply_le t (U.symm x)
  continuous_orbit x := by
    change Continuous (fun t => U (T t (U.symm x)))
    exact U.continuous.comp (T.continuous_orbit _)

/-- Conjugation transports the complete generator graph. -/
theorem u7_conjugated_semigroup_generator {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (U : E ≃ₗᵢ[ℝ] F) (v : T.generatorDomain) :
    ∃ hv : U v ∈ (u7ConjugatedSemigroup T U).generatorDomain,
      (u7ConjugatedSemigroup T U).generator ⟨U v, hv⟩ = U (T.generator v) := by
  let S := u7ConjugatedSemigroup T U
  have h : Filter.Tendsto (S.differenceQuotient (U v)) (𝓝[>] 0) (𝓝 (U (T.generator v))) := by
    have ht := U.continuous.tendsto (T.generator v) |>.comp (T.tendsto_generator v)
    convert ht using 1
    ext t
    simp [MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.differenceQuotient,
      S, u7ConjugatedSemigroup, map_smul, map_sub]
  refine ⟨S.mem_generatorDomain_of_tendsto h, ?_⟩
  exact S.generator_eq_of_tendsto _ h

/-- Positivity is preserved by conjugation with a positive order isomorphism. -/
theorem u7_conjugated_semigroup_positive
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (T : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (Lp ℝ 2 μ))
    (U : Lp ℝ 2 μ ≃ₗᵢ[ℝ] Lp ℝ 2 ν)
    (hU : ∀ v, 0 ≤ v → 0 ≤ U v) (hUinv : ∀ v, 0 ≤ v → 0 ≤ U.symm v)
    (hT : ∀ (t : ℝ≥0) v, 0 ≤ v → 0 ≤ T t v)
    (t : ℝ≥0) (v : Lp ℝ 2 ν) (hv : 0 ≤ v) :
    0 ≤ u7ConjugatedSemigroup T U t v := by
  change 0 ≤ U (T t (U.symm v))
  exact hU _ (hT t _ (hUinv v hv))

#print axioms u7_conjugated_semigroup_generator
#print axioms u7_conjugated_semigroup_positive

end EinsteinFull
