import EinsteinFull.Calculus.U6RegularPathRealization
import EinsteinFull.Calculus.C4FoundationPhysicalLawUniqueness

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

noncomputable section
namespace EinsteinFull
open Blueprint

/-- Every realization of the regular kernel starts at its specified point. -/
theorem u6_regular_realization_ae_initial
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d))
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) : ∀ᵐ γ ∂K x, γ 0 = x := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  have hmarg : (K x).map (fun γ : Path d => γ 0) = Measure.dirac x := by
    have h := SubdiffusiveProcess.map_eval_eq_of_finsetEvaluation P (K x) x 0 (by
      have h := congrArg (fun k => k x) (hfdd {0})
      simpa only [Kernel.map_apply _
        (MarkovProcess.ContinuousPath.measurable_finsetEvaluation _)] using h)
    simpa only [P, MarkovProcess.SubMarkovKernelSemigroup.kernel_zero,
      Kernel.id_apply] using h
  have hmeas : Measurable (fun γ : Path d => γ 0) := measurable_pathPosition 0
  apply (ae_map_iff hmeas.aemeasurable (measurableSet_singleton x)).mp
  rw [hmarg, ae_dirac_eq]
  exact Filter.mem_pure.mpr rfl

/-- The regular compact-test generator is time-integrable along every path. -/
theorem u6_regular_generator_path_intervalIntegrable
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (γ : Path d) (t : ℝ≥0) :
    IntervalIntegrable (fun u : ℝ =>
      physicalGenerator (firstCoordinateIndex hd) ω lam f (γ u.toNNReal)) volume 0 t := by
  obtain ⟨D, hD, hb⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc
  have hm : Measurable (fun u : ℝ =>
      physicalGenerator (firstCoordinateIndex hd) ω lam f (γ u.toNNReal)) :=
    (measurable_physicalGenerator (firstCoordinateIndex hd) ω lam f).comp
      (γ.continuous.comp continuous_real_toNNReal).measurable
  apply (intervalIntegrable_const (c := D)).mono_fun hm.aestronglyMeasurable
  filter_upwards with u
  simpa only [Real.norm_eq_abs, Real.norm_of_nonneg hD] using hb (γ u.toNNReal)

/-- The bounded measurable generator correction is measurable at its terminal time. -/
theorem u6_regular_generator_integral_stronglyMeasurable
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ)
    (f : Vec d → ℝ) (t : ℝ≥0) :
    StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) t]
      (fun γ : Path d => ∫ s in (0 : ℝ)..(t : ℝ),
        physicalGenerator (firstCoordinateIndex hd) ω lam f (γ s.toNNReal)) := by
  have hprod : StronglyMeasurable[(borel ℝ).prod
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) t)]
      (fun p : ℝ × Path d => physicalGenerator (firstCoordinateIndex hd) ω lam f
        (p.2 (min (Real.toNNReal p.1) t))) := by
    exact ((measurable_physicalGenerator (firstCoordinateIndex hd) ω lam f).comp
      (MarkovProcess.ContinuousPath.measurable_clampedCoordinate (alpha := Vec d) t)).stronglyMeasurable
  have h := MarkovProcess.SubMarkovKernelSemigroup.stronglyMeasurable_integral_prod
    (volume.restrict (Set.Ioc (0 : ℝ) t)) hprod
  have heq : (fun γ : Path d => ∫ s in (0 : ℝ)..(t : ℝ),
      physicalGenerator (firstCoordinateIndex hd) ω lam f (γ s.toNNReal)) =
      (fun γ : Path d => ∫ s, physicalGenerator (firstCoordinateIndex hd) ω lam f
        (γ (min (Real.toNNReal s) t)) ∂(volume.restrict (Set.Ioc (0 : ℝ) t))) := by
    funext γ
    rw [intervalIntegral.integral_of_le t.coe_nonneg]
    refine setIntegral_congr_fun measurableSet_Ioc fun s hs => ?_
    rw [min_eq_left (Real.toNNReal_le_iff_le_coe.mpr hs.2)]
  rw [heq]
  exact h

/-- The regular Dynkin process, using the literal physical generator. -/
def u6RegularDynkinProcess {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (f : Vec d → ℝ) (t : ℝ≥0) (γ : Path d) : ℝ :=
  f (γ t) - ∫ s in (0 : ℝ)..(t : ℝ),
    physicalGenerator (firstCoordinateIndex hd) ω lam f (γ s.toNNReal)

/-- The regular Dynkin process is measurable for the canonical filtration. -/
theorem u6_regular_dynkinProcess_stronglyMeasurable
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ)
    (f : Vec d → ℝ) (hf : Continuous f) (t : ℝ≥0) :
    StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) t]
      (u6RegularDynkinProcess hd ω lam f t) := by
  exact (hf.comp_stronglyMeasurable
    (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
      (alpha := Vec d) t).stronglyMeasurable).sub
    (u6_regular_generator_integral_stronglyMeasurable hd ω lam f t)

/-- A compact-test Dynkin process is uniformly bounded at each fixed time. -/
theorem u6_regular_dynkinProcess_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (t : ℝ≥0) : ∃ C : ℝ, ∀ γ : Path d, ‖u6RegularDynkinProcess hd ω lam f t γ‖ ≤ C := by
  let F := gmpPhysicalCompactC0 f hf.continuous hc
  obtain ⟨D, _, hb⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc
  refine ⟨‖F‖ + (t : ℝ) * D, fun γ => ?_⟩
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := (t : ℝ)) (C := D)
    (f := fun s : ℝ => physicalGenerator (firstCoordinateIndex hd) ω lam f (γ s.toNNReal))
    (fun s _ => by simpa only [Real.norm_eq_abs] using hb (γ s.toNNReal))
  rw [sub_zero, abs_of_nonneg t.coe_nonneg, mul_comm] at hi
  change ‖f (γ t) - _‖ ≤ _
  exact (norm_sub_le _ _).trans (add_le_add
    (MarkovProcess.SubMarkovKernelSemigroup.norm_c0_apply_le F (γ t)) hi)

#print axioms u6_regular_dynkinProcess_stronglyMeasurable
#print axioms u6_regular_dynkinProcess_bound

/-- The regular Dynkin process decomposes at any deterministic time. -/
theorem u6_regular_dynkinProcess_eq_add_shift
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hc : HasCompactSupport f)
    (s t : ℝ≥0) (hst : s ≤ t) (γ : Path d) :
    u6RegularDynkinProcess hd ω lam f t γ =
      u6RegularDynkinProcess hd ω lam f s γ - f (γ s) +
        u6RegularDynkinProcess hd ω lam f (t - s)
          (MarkovProcess.ContinuousPath.shift s γ) := by
  let g : ℝ → ℝ := fun v => physicalGenerator (firstCoordinateIndex hd) ω lam f (γ v.toNNReal)
  have hs := u6_regular_generator_path_intervalIntegrable hd ω lam Λ hΛ hω f hf hc γ s
  have ht := u6_regular_generator_path_intervalIntegrable hd ω lam Λ hΛ hω f hf hc γ t
  have hstint : IntervalIntegrable g volume (s : ℝ) (t : ℝ) := hs.symm.trans ht
  have hshift : (∫ u in (0 : ℝ)..((t - s : ℝ≥0) : ℝ),
      physicalGenerator (firstCoordinateIndex hd) ω lam f (γ (s + Real.toNNReal u))) =
      ∫ v in (s : ℝ)..(t : ℝ), g v := by
    have hcongr : (∫ u in (0 : ℝ)..((t - s : ℝ≥0) : ℝ),
        physicalGenerator (firstCoordinateIndex hd) ω lam f (γ (s + Real.toNNReal u))) =
        ∫ u in (0 : ℝ)..((t - s : ℝ≥0) : ℝ), g (u + s) := by
      refine intervalIntegral.integral_congr fun u hu => ?_
      have hu0 : (0 : ℝ) ≤ u := by
        rw [Set.uIcc_of_le (t - s : ℝ≥0).coe_nonneg] at hu
        exact hu.1
      have hcoe : Real.toNNReal (u + s) = s + Real.toNNReal u := by
        apply NNReal.coe_injective
        rw [NNReal.coe_add, Real.coe_toNNReal u hu0,
          Real.coe_toNNReal _ (add_nonneg hu0 s.coe_nonneg)]
        ring
      simp only [g, hcoe]
    rw [hcongr, intervalIntegral.integral_comp_add_right g (s : ℝ), zero_add]
    congr 1
    rw [NNReal.coe_sub hst]
    ring
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hs hstint
  simp only [u6RegularDynkinProcess, MarkovProcess.ContinuousPath.shift_apply,
    add_tsub_cancel_of_le hst]
  rw [hshift]
  linarith only [hsplit]

#print axioms u6_regular_dynkinProcess_eq_add_shift

/-- The realization has the compact-test Dynkin identity in expectation. -/
theorem u6_regular_realization_dynkin_expectation
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
        physicalReversibleMeasure ω hd lam)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) (t : ℝ≥0) :
    (∫ γ, f (γ t) ∂K x) - f x =
      ∫ γ, (∫ s in (0 : ℝ)..(t : ℝ),
        physicalGenerator (firstCoordinateIndex hd) ω lam f (γ s.toNNReal)) ∂K x := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  have hmarg (s : ℝ≥0) : (K x).map (fun γ : Path d => γ s) = P s x := by
    have h := congrArg (fun k => k x)
      (SubdiffusiveProcess.Section10.realization_map_eval P
        (u2_regular_kernel_conservative hd ω lam Λ hΛ hω) K hfdd s)
    have hm : Measurable (fun γ : Path d => γ s) := measurable_pathPosition s
    rw [← Kernel.map_apply K hm]
    exact h
  have heval (s : ℝ≥0) : (∫ γ, f (γ s) ∂K x) = ∫ y, f y ∂P s x := by
    rw [← hmarg s]
    exact (integral_map (measurable_pathPosition s).aemeasurable hf.continuous.aestronglyMeasurable).symm
  have hgen (s : ℝ) : (∫ γ, physicalGenerator (firstCoordinateIndex hd) ω lam f
      (γ s.toNNReal) ∂K x) = ∫ y, physicalGenerator (firstCoordinateIndex hd) ω lam f y
        ∂P s.toNNReal x := by
    rw [← hmarg s.toNNReal]
    exact (integral_map (measurable_pathPosition s.toNNReal).aemeasurable
      (measurable_physicalGenerator (firstCoordinateIndex hd) ω lam f).aestronglyMeasurable).symm
  obtain ⟨D, _, hb⟩ := sbxS4_physicalGenerator_bounded hd (firstCoordinateIndex hd)
    (lt_of_lt_of_le zero_lt_one hΛ) hω lam hf hc
  have hm : Measurable (fun p : ℝ × Path d =>
      physicalGenerator (firstCoordinateIndex hd) ω lam f (p.2 p.1.toNNReal)) :=
    (measurable_physicalGenerator (firstCoordinateIndex hd) ω lam f).comp
      ((continuous_eval.comp continuous_swap).comp
        (continuous_real_toNNReal.fst'.prodMk continuous_snd)).measurable
  have hi : Integrable (fun p : ℝ × Path d =>
      physicalGenerator (firstCoordinateIndex hd) ω lam f (p.2 p.1.toNNReal))
      ((volume.restrict (Set.Ioc (0 : ℝ) t)).prod (K x)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable D
    filter_upwards with p
    simpa only [Real.norm_eq_abs] using hb (p.2 p.1.toNNReal)
  calc
    (∫ γ, f (γ t) ∂K x) - f x =
        ∫ s in (0 : ℝ)..(t : ℝ), ∫ y,
          physicalGenerator (firstCoordinateIndex hd) ω lam f y ∂P s.toNNReal x := by
      rw [heval]
      exact u8_regular_compactTest_dynkin_of_ac hd ω lam Λ hΛ hω hac f hf hc t x
    _ = ∫ s in (0 : ℝ)..(t : ℝ), ∫ γ,
        physicalGenerator (firstCoordinateIndex hd) ω lam f (γ s.toNNReal) ∂K x := by
      apply intervalIntegral.integral_congr
      intro s _
      exact (hgen s).symm
    _ = ∫ γ, (∫ s in (0 : ℝ)..(t : ℝ),
        physicalGenerator (firstCoordinateIndex hd) ω lam f (γ s.toNNReal)) ∂K x := by
      rw [intervalIntegral.integral_of_le t.coe_nonneg, integral_integral_swap hi]
      refine integral_congr_ae (Filter.Eventually.of_forall fun γ => ?_)
      exact (intervalIntegral.integral_of_le t.coe_nonneg).symm

/-- The finite-dimensional realization carries the compact-test Dynkin martingale. -/
theorem u6_regular_realization_compact_martingale
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
        physicalReversibleMeasure ω hd lam)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hc : HasCompactSupport f) :
    Martingale (u6RegularDynkinProcess hd ω lam f)
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) (K x) := by
  let M := u6RegularDynkinProcess hd ω lam f
  let F := gmpPhysicalCompactC0 f hf.continuous hc
  have hM (t : ℝ≥0) := u6_regular_dynkinProcess_stronglyMeasurable hd ω lam f hf.continuous t
  have hintM (t : ℝ≥0) (y : Vec d) : Integrable (M t) (K y) := by
    obtain ⟨C, hC⟩ := u6_regular_dynkinProcess_bound hd ω lam Λ hΛ hω f hf hc t
    exact Integrable.of_bound ((hM t).mono
      ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le t)).aestronglyMeasurable C
      (Filter.Eventually.of_forall hC)
  have hmean (t : ℝ≥0) (y : Vec d) : ∫ γ, M t γ ∂K y = f y := by
    have hpos : Integrable (fun γ : Path d => f (γ t)) (K y) := by
      apply Integrable.of_bound (hf.continuous.measurable.comp (measurable_pathPosition t)).aestronglyMeasurable ‖F‖
      exact Filter.Eventually.of_forall fun γ =>
        MarkovProcess.SubMarkovKernelSemigroup.norm_c0_apply_le F (γ t)
    have hcorr : Integrable (fun γ : Path d => ∫ s in (0 : ℝ)..(t : ℝ),
        physicalGenerator (firstCoordinateIndex hd) ω lam f (γ s.toNNReal)) (K y) := by
      have h := hpos.sub (hintM t y)
      convert h using 1
      funext γ
      simp only [Pi.sub_apply, M, u6RegularDynkinProcess]
      ring
    have he := u6_regular_realization_dynkin_expectation hd ω lam Λ hΛ hω hac K hfdd y f hf hc t
    change (∫ γ, f (γ t) - (∫ s in (0 : ℝ)..(t : ℝ),
      physicalGenerator (firstCoordinateIndex hd) ω lam f (γ s.toNNReal)) ∂K y) = f y
    rw [integral_sub hpos hcorr]
    linarith
  refine ⟨fun t => hM t, fun s t hst => ?_⟩
  have hdecomp : M t = (fun γ : Path d => M s γ - f (γ s)) +
      fun γ => M (t - s) (MarkovProcess.ContinuousPath.shift s γ) := by
    funext γ
    exact u6_regular_dynkinProcess_eq_add_shift hd ω lam Λ hΛ hω f hf hc s t hst γ
  have hmeasA : StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s]
      (fun γ : Path d => M s γ - f (γ s)) :=
    (hM s).sub (hf.continuous.comp_stronglyMeasurable
      (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
        (alpha := Vec d) s).stronglyMeasurable)
  have hintA : Integrable (fun γ : Path d => M s γ - f (γ s)) (K x) := by
    apply (hintM s x).sub
    apply Integrable.of_bound (hf.continuous.measurable.comp (measurable_pathPosition s)).aestronglyMeasurable ‖F‖
    exact Filter.Eventually.of_forall fun γ =>
      MarkovProcess.SubMarkovKernelSemigroup.norm_c0_apply_le F (γ s)
  obtain ⟨C, hC⟩ := u6_regular_dynkinProcess_bound hd ω lam Λ hΛ hω f hf hc (t - s)
  have hmeasF := (hM (t - s)).mono
    ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le (t - s))
  have hintB : Integrable (fun γ : Path d => M (t - s) (MarkovProcess.ContinuousPath.shift s γ)) (K x) :=
    Integrable.of_bound (hmeasF.comp_measurable
      (MarkovProcess.ContinuousPath.measurable_shift_fixed (alpha := Vec d) s)).aestronglyMeasurable C
      (Filter.Eventually.of_forall fun γ => hC _)
  have hcondA := condExp_of_stronglyMeasurable
    ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le s) hmeasA hintA
  have hcondB := SubdiffusiveProcess.Section10.condExp_shift_realization
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω)
    (u2_regular_kernel_conservative hd ω lam Λ hΛ hω)
    (u2RegularC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω)
    K hfdd x s (M (t - s)) hmeasF C hC
  have hcondB' : (K x)[fun γ : Path d => M (t - s) (MarkovProcess.ContinuousPath.shift s γ)|
      MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s] =ᵐ[K x]
      fun γ : Path d => f (γ s) := by
    exact hcondB.trans (Filter.Eventually.of_forall fun γ => hmean (t - s) (γ s))
  change (K x)[M t | MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s] =ᵐ[K x] M s
  rw [hdecomp]
  refine (condExp_add hintA hintB _).trans ?_
  rw [hcondA]
  refine (Filter.EventuallyEq.add (Filter.EventuallyEq.refl _ _) hcondB').trans ?_
  filter_upwards with γ
  dsimp
  ring

/-- The unforced regular continuous realization solves the physical martingale problem. -/
theorem u6_regular_unforced_continuous_kernel_and_mp {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ K : ProbabilityTheory.Kernel (Vec d) (Path d), ProbabilityTheory.IsMarkovKernel K ∧
      (∀ I : Finset ℝ≥0,
        K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
          MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
            (u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω) I) ∧
      ∀ x, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω 0) x (K x) := by
  have hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≪ physicalReversibleMeasure ω hd 0 := by
    intro t ht x
    obtain ⟨M, hM, hdom⟩ := u2_regular_unforced_kernel_domination hd ω Λ hΛ hω t ht
    exact (Measure.absolutelyContinuous_of_le_smul (hdom x)).trans
      (Measure.absolutelyContinuous_of_le_smul (u4_unforced_physical_measure_comparable hd ω Λ hω).2)
  obtain ⟨K, hK, hfdd⟩ := u6_regular_unforced_continuous_kernel_exists hd ω Λ hΛ hω
  let : IsMarkovKernel K := hK
  refine ⟨K, hK, hfdd, fun x => ?_⟩
  refine ⟨inferInstance, u6_regular_realization_ae_initial hd ω 0 Λ hΛ hω K hfdd x, ?_⟩
  intro f hf hc
  have hM := u6_regular_realization_compact_martingale hd ω 0 Λ hΛ hω hac K hfdd x f hf hc
  rw [← c4_pathFiltration_eq_canonical d] at hM
  have hM0 := martingale_const_fun (pathFiltration d) (K x)
    (hM.stronglyAdapted 0) (hM.integrable 0)
  have hcomp : Martingale (compensatedTest (physicalGenerator (firstCoordinateIndex hd) ω 0) f)
      (pathFiltration d) (K x) := by
    convert hM.sub hM0 using 1
    funext t γ
    simp only [compensatedTest, u6RegularDynkinProcess, NNReal.coe_zero,
      intervalIntegral.integral_same, sub_zero, Pi.sub_apply]
    ring
  refine ⟨?_, fun t => hcomp.integrable t, hcomp⟩
  intro t
  exact Filter.Eventually.of_forall fun γ =>
    u6_regular_generator_path_intervalIntegrable hd ω 0 Λ hΛ hω f hf hc γ t

/-- The unforced regular physical kernel has a full fixed-environment realization. -/
theorem u6_regular_unforced_fixed_environment_realization_exists
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) :
    Nonempty (GantertFixedEnvironmentRealization hd Λ hΛ ω hω 0 (by norm_num) (by norm_num)) := by
  obtain ⟨K, hK, hfdd, _⟩ := u6_regular_unforced_continuous_kernel_and_mp hd ω Λ hΛ hω
  let : IsMarkovKernel K := hK
  have hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≪ (volume : Measure (Vec d)) := by
    intro t ht x
    obtain ⟨M, p, hM, hp, hpb, hrep⟩ :=
      u2_regular_unforced_kernel_bounded_density hd ω Λ hΛ hω t ht
    rw [hrep x]
    exact withDensity_absolutelyContinuous _ _
  obtain ⟨R, _, _⟩ := u2_regular_fixed_environment_realization_of_ac_fdd
    hd ω 0 Λ hΛ hω (by norm_num) (by norm_num) K hfdd hac
  exact ⟨R⟩

/-- A supplied law with absolutely continuous occupation is the law of the
actual unforced fixed-environment realization. -/
private theorem u6_occupation_ac_of_marginals {d : ℕ}
    (P : Measure (Path d)) [IsProbabilityMeasure P]
    (h : ∀ t : ℝ≥0, 0 < t →
      P.map (pathPosition t) ≪ (volume : Measure (Vec d))) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  refine Measure.AbsolutelyContinuous.mk fun N hN hnull => ?_
  have hsection : ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ∀ᵐ γ ∂P, γ t.toNNReal ∉ N := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
    have hz : (P.map (pathPosition t.toNNReal)) N = 0 := (h _ ht') hnull
    exact (ae_map_iff (measurable_pathPosition _).aemeasurable hN.compl).mp
      (measure_eq_zero_iff_ae_notMem.mp hz)
  have hprod : ∀ᵐ z ∂(volume.restrict (Set.Ioi (0 : ℝ))).prod P,
      z.2 z.1.toNNReal ∉ N := by
    apply (Measure.ae_prod_iff_ae_ae ?_).2 hsection
    exact ((hN.preimage heval).compl).preimage measurable_swap
  have hswap : ∀ᵐ z ∂P.prod (volume.restrict (Set.Ioi (0 : ℝ))),
      z.1 z.2.toNNReal ∉ N :=
    Measure.measurePreserving_swap.quasiMeasurePreserving.ae hprod
  rw [Measure.map_apply heval hN]
  exact measure_eq_zero_iff_ae_notMem.mpr hswap

/-- Identification when the supplied law has absolutely continuous occupation. -/
theorem u6_regular_unforced_supplied_law_identification_of_occupation_ac
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (x : Vec d)
    (P : Measure (Path d))
    (hP : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω 0) x P)
    (hocc : Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) :
    ∃ R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω 0 (by norm_num) (by norm_num),
      P = R.pathLaw x := by
  obtain ⟨K, hK, hfdd, hMP⟩ := u6_regular_unforced_continuous_kernel_and_mp hd ω Λ hΛ hω
  let : IsMarkovKernel K := hK
  have hac : ∀ (t : ℝ≥0), 0 < t → ∀ y,
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t y ≪ (volume : Measure (Vec d)) := by
    intro t ht y
    obtain ⟨M, p, hM, hp, hpb, hrep⟩ :=
      u2_regular_unforced_kernel_bounded_density hd ω Λ hΛ hω t ht
    rw [hrep y]
    exact withDensity_absolutelyContinuous _ _
  obtain ⟨R, hRK, hRP⟩ := u2_regular_fixed_environment_realization_of_ac_fdd
    hd ω 0 Λ hΛ hω (by norm_num) (by norm_num) K hfdd hac
  let : IsProbabilityMeasure (R.pathLaw x) := by rw [hRK]; infer_instance
  have hmarg : ∀ t : ℝ≥0, 0 < t →
      (R.pathLaw x).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
    intro t ht
    rw [R.pathLaw_endpoint, hRP]
    exact hac t ht x
  have hRocc := u6_occupation_ac_of_marginals (R.pathLaw x) hmarg
  have hΛpos : 0 < Λ := lt_of_lt_of_le zero_lt_one hΛ
  have hRphys : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω 0)
      x (R.pathLaw x) := by rw [hRK]; exact hMP x
  have hPtext := c4_textbook_solves_of_physical_and_averaged_occupation
    hΛpos hω (firstCoordinateIndex hd) 0 hP hocc
  have hRtext := c4_textbook_solves_of_physical_and_averaged_occupation
    hΛpos hω (firstCoordinateIndex hd) 0 hRphys hRocc
  obtain ⟨hc, hs, hb, he, hm, hbd⟩ :=
    physical_svHypotheses hΛpos hω (firstCoordinateIndex hd) 0
  obtain ⟨S, _, hu⟩ := foundation_textbook_well_posed d (by omega)
    (⇑ω.1) (physicalDrift ω (firstCoordinateIndex hd) 0) hc hs hb he hm hbd x
  exact ⟨R, (hu _ hPtext).trans (hu _ hRtext).symm⟩

/-- Every fixed-environment realization has absolutely continuous occupation. -/
theorem u6_fixed_environment_realization_occupation_ac
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (x : Vec d) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      ((R.pathLaw x).prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  let : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  apply u6_occupation_ac_of_marginals
  intro t ht
  rw [R.pathLaw_endpoint, R.transitionKernel_eq_heatKernel t ht x]
  exact withDensity_absolutelyContinuous _ _

/-- The remaining issue in supplied-law identification is precisely the
absolute continuity of that same law's averaged occupation measure. -/
theorem u6_regular_unforced_supplied_law_identification_iff_occupation_ac
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (ω : FieldPair d) (hω : IsRegular Λ ω) (x : Vec d)
    (P : Measure (Path d))
    (hP : SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω 0) x P) :
    (∃ R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω 0 (by norm_num) (by norm_num),
      P = R.pathLaw x) ↔
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  constructor
  · rintro ⟨R, rfl⟩
    exact u6_fixed_environment_realization_occupation_ac hd hΛ ω hω 0
      (by norm_num) (by norm_num) R x
  · exact u6_regular_unforced_supplied_law_identification_of_occupation_ac hd hΛ ω hω x P hP

#print axioms u6_regular_unforced_supplied_law_identification_iff_occupation_ac
#print axioms u6_fixed_environment_realization_occupation_ac
#print axioms u6_regular_unforced_supplied_law_identification_of_occupation_ac

#print axioms u6_regular_unforced_fixed_environment_realization_exists
#print axioms u6_regular_unforced_continuous_kernel_and_mp

#print axioms u6_regular_realization_compact_martingale

#print axioms u6_regular_realization_dynkin_expectation
#print axioms u6_regular_generator_integral_stronglyMeasurable
#print axioms u6_regular_realization_ae_initial
#print axioms u6_regular_generator_path_intervalIntegrable
end EinsteinFull
