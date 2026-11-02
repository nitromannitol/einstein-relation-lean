import EinsteinFull.Calculus.U7RegularKernelDensity

open EinsteinRelation EinsteinRelation.SpatialDirichlet MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

namespace EinsteinFull

/-- A finite kernel with an arbitrary measurable parameter has a jointly
measurable nonnegative real density when all its measures are absolutely continuous. -/
theorem u6_parameter_kernel_real_density {α : Type*} [MeasurableSpace α] {d : ℕ}
    (K : Kernel α (Vec d)) [IsFiniteKernel K]
    (hK : ∀ x, K x ≪ (volume : Measure (Vec d))) :
    ∃ p : α → Vec d → ℝ, Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y) ∧
      ∀ x, K x = volume.withDensity (fun y => ENNReal.ofReal (p x y)) := by
  let μ : Measure (Vec d) := volume
  let ν := μ.toFinite
  let η : Kernel α (Vec d) := Kernel.const _ ν
  let q := ν.rnDeriv μ
  let r : α → Vec d → ℝ≥0∞ := fun x y => q y * K.rnDeriv η x y
  have hq : Measurable q := Measure.measurable_rnDeriv _ _
  have hr : Measurable (Function.uncurry r) :=
    (hq.comp measurable_snd).mul (Kernel.measurable_rnDeriv K η)
  have hrep (x : α) : K x = μ.withDensity (r x) := by
    have hν : μ.withDensity q = ν := Measure.withDensity_rnDeriv_eq ν μ
      (toFinite_absolutelyContinuous μ)
    have hKν : K x ≪ ν := (hK x).trans (absolutelyContinuous_toFinite μ)
    have heq := Kernel.withDensity_rnDeriv_eq (κ := K) (η := η) hKν
    rw [Kernel.withDensity_apply η (Kernel.measurable_rnDeriv K η)] at heq
    change ν.withDensity (K.rnDeriv η x) = K x at heq
    change K x = μ.withDensity (fun y => q y * K.rnDeriv η x y)
    rw [show (fun y => q y * K.rnDeriv η x y) = q * K.rnDeriv η x by rfl,
      withDensity_mul μ hq (Kernel.measurable_rnDeriv_right K η x), hν]
    exact heq.symm
  refine ⟨fun x y => (r x y).toReal, ENNReal.measurable_toReal.comp hr,
    fun x y => ENNReal.toReal_nonneg, fun x => ?_⟩
  have hrx : Measurable (r x) := hr.comp (measurable_const.prodMk measurable_id)
  have hfin : (∫⁻ y, r x y ∂μ) ≠ ∞ := by
    have hm : μ.withDensity (r x) Set.univ ≠ ∞ := by
      rw [← hrep x]
      exact measure_ne_top (K x) Set.univ
    simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using hm
  have hae := ae_lt_top hrx hfin
  change K x = μ.withDensity _
  rw [hrep x]
  apply withDensity_congr_ae
  filter_upwards [hae] with y hy
  exact (ENNReal.ofReal_toReal hy.ne).symm

/-- Normalization of a jointly measurable density of a Markov kernel. -/
theorem u6_parameter_kernel_density_normalized {α : Type*} [MeasurableSpace α] {d : ℕ}
    (K : Kernel α (Vec d)) [IsMarkovKernel K] (q : α → Vec d → ℝ)
    (hq : Measurable (Function.uncurry q)) (hn : ∀ x y, 0 ≤ q x y)
    (hr : ∀ x, K x = volume.withDensity (fun y => ENNReal.ofReal (q x y))) :
    ∀ x, Integrable (q x) volume ∧ ∫ y, q x y = 1 := by
  intro x
  have hqm : Measurable (q x) := hq.comp (measurable_const.prodMk measurable_id)
  have hm : (∫⁻ y, ENNReal.ofReal (q x y) ∂(volume : Measure (Vec d))) = 1 := by
    have he := congrArg (fun μ : Measure (Vec d) => μ Set.univ) (hr x)
    simpa only [measure_univ, withDensity_apply _ MeasurableSet.univ,
      Measure.restrict_univ] using he.symm
  have hf : Integrable (fun y => (ENNReal.ofReal (q x y)).toReal) volume :=
    integrable_toReal_of_lintegral_ne_top hqm.ennreal_ofReal.aemeasurable (by rw [hm]; simp)
  have hi : Integrable (q x) volume := by
    simpa only [ENNReal.toReal_ofReal (hn x _)] using hf
  refine ⟨hi, ?_⟩
  have he := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (hn x))
  rw [hm] at he
  have := congrArg ENNReal.toReal he
  simpa only [ENNReal.toReal_ofReal (integral_nonneg (hn x)), ENNReal.toReal_one] using this

/-- The regular transition semigroup as a joint time-start kernel. -/
noncomputable def u6FullTimeKernel {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    Kernel (ℝ≥0 × Vec d) (Vec d) := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  exact ⟨fun z => P z.1 z.2, P.measurable_toMeasure⟩

/-- Time zero is replaced by one when selecting densities. -/
noncomputable def u6PositiveTime (t : ℝ≥0) : ℝ≥0 := if t = 0 then 1 else t

theorem u6_positiveTime_measurable : Measurable u6PositiveTime :=
  measurable_const.piecewise (measurableSet_singleton 0) measurable_id

/-- The time-start kernel with a positive time at every parameter. -/
noncomputable def u6PositiveTimeKernel {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    Kernel (ℝ≥0 × Vec d) (Vec d) :=
  (u6FullTimeKernel hd ω lam Λ hΛ hω).comap
    (fun z => (u6PositiveTime z.1, z.2))
    ((u6_positiveTime_measurable.comp measurable_fst).prodMk measurable_snd)

instance u6PositiveTimeKernel_markov {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    IsMarkovKernel (u6PositiveTimeKernel hd ω lam Λ hΛ hω) := by
  refine ⟨fun z => ⟨?_⟩⟩
  exact u2_regular_kernel_conservative hd ω lam Λ hΛ hω _ _

theorem u6_positiveTimeKernel_ac {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (z : ℝ≥0 × Vec d) : u6PositiveTimeKernel hd ω lam Λ hΛ hω z ≪
      (volume : Measure (Vec d)) := by
  change u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (if z.1 = 0 then 1 else z.1) z.2 ≪ _
  apply u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω
  split_ifs with h
  · exact zero_lt_one
  · exact lt_of_le_of_ne (bot_le : 0 ≤ z.1) (Ne.symm h)

theorem u6_positiveTimeKernel_apply {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    u6PositiveTimeKernel hd ω lam Λ hΛ hω (t, x) =
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x := by
  simp [u6PositiveTimeKernel, u6FullTimeKernel, u6PositiveTime, ne_of_gt ht]

/-- The signed regular transition kernels possess one jointly measurable
normalized density for all positive times and starting points. -/
theorem u6_regular_signed_joint_time_space_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ p : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) ∧
      (∀ t x y, 0 ≤ p t x y) ∧
      ∀ (t : ℝ≥0), 0 < t → ∀ x : Vec d,
        Integrable (p t x) volume ∧ (∫ y, p t x y) = 1 ∧
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          volume.withDensity (fun y => ENNReal.ofReal (p t x y)) := by
  let K := u6PositiveTimeKernel hd ω lam Λ hΛ hω
  obtain ⟨q, hq, hn, hr⟩ := u6_parameter_kernel_real_density K
    (u6_positiveTimeKernel_ac hd ω lam Λ hΛ hω)
  have hnorm := u6_parameter_kernel_density_normalized K q hq hn hr
  let p : ℝ≥0 → Vec d → Vec d → ℝ := fun t x y => if t = 0 then 0 else q (t, x) y
  have hqjoint : Measurable (fun z : ℝ≥0 × Vec d × Vec d => q (z.1, z.2.1) z.2.2) :=
    hq.comp ((measurable_fst.prodMk (measurable_fst.comp measurable_snd)).prodMk
      (measurable_snd.comp measurable_snd))
  have hp : Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) :=
    measurable_const.piecewise ((measurable_fst (measurableSet_singleton 0))) hqjoint
  refine ⟨p, hp, ?_, ?_⟩
  · intro t x y
    dsimp [p]
    split_ifs
    · exact le_rfl
    · exact hn (t, x) y
  · intro t ht x
    have hrep : u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (q (t, x) y)) := by
      rw [← u6_positiveTimeKernel_apply hd ω lam Λ hΛ hω t ht x]
      exact hr (t, x)
    refine ⟨?_, ?_, ?_⟩
    · simpa [p, ne_of_gt ht] using (hnorm (t, x)).1
    · simpa [p, ne_of_gt ht] using (hnorm (t, x)).2
    · simpa [p, ne_of_gt ht] using hrep

#print axioms u6_regular_signed_joint_time_space_density


/-- The supplied path law has the explicit joint time-position density. -/
theorem u6_regular_signed_same_FDD_joint_occupation_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ p : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) ∧
      (∀ t x y, 0 ≤ p t x y) ∧
      ∀ (x : Vec d) (T : ℝ≥0),
        Measure.map (fun z : ℝ × Path d => (z.1, z.2 z.1.toNNReal))
          ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod (K x)) =
        (((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod
          (volume : Measure (Vec d))).withDensity
            (fun z : ℝ × Vec d => ENNReal.ofReal (p z.1.toNNReal x z.2))) := by
  obtain ⟨p, hp, hn, hrep⟩ := u6_regular_signed_joint_time_space_density hd ω lam Λ hΛ hω
  refine ⟨p, hp, hn, ?_⟩
  intro x T
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))
  let F : ℝ × Path d → ℝ × Vec d := fun z => (z.1, z.2 z.1.toNNReal)
  let q : ℝ × Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal (p z.1.toNNReal x z.2)
  have hF : Measurable F := measurable_fst.prodMk ((continuous_eval.comp
    (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable)
  have hq : Measurable q := (hp.comp (((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
    (measurable_const.prodMk measurable_snd)))).ennreal_ofReal
  ext S hS
  rw [Measure.map_apply hF hS, Measure.prod_apply (hS.preimage hF),
    withDensity_apply _ hS]
  rw [← lintegral_indicator hS, lintegral_prod _ (hq.indicator hS).aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hmarg := Blueprint.k11_endpoint (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω)
    K hfdd t.toNNReal x
  rw [(hrep t.toNNReal (Real.toNNReal_pos.mpr ht.1) x).2.2] at hmarg
  have hs : MeasurableSet (Prod.mk t ⁻¹' S) := measurable_prodMk_left hS
  have he := congrArg (fun ν : Measure (Vec d) => ν (Prod.mk t ⁻¹' S)) hmarg
  rw [Measure.map_apply (measurable_pathPosition _) hs, withDensity_apply _ hs] at he
  rw [← lintegral_indicator hs] at he
  convert he using 1
  · congr 1
  · apply lintegral_congr
    intro y
    by_cases hy : (t, y) ∈ S <;> simp [q, Set.indicator, hy]

#print axioms u6_regular_signed_same_FDD_joint_occupation_density


/-- Discounted occupation of a supplied law with the canonical finite-dimensional laws. -/
theorem u6_regular_signed_discounted_occupation_formula
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I) :
    ∃ p : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) ∧
      (∀ t x y, 0 ≤ p t x y) ∧
      ∀ (x : Vec d) (α : ℝ) (F : ℝ × Vec d → ℝ≥0∞), Measurable F →
        (∫⁻ t : ℝ in Set.Ioi 0, ENNReal.ofReal (Real.exp (-α * t)) *
          ∫⁻ γ : Path d, F (t, γ t.toNNReal) ∂K x) =
        ∫⁻ z : ℝ × Vec d, ENNReal.ofReal (Real.exp (-α * z.1)) * F z *
          ENNReal.ofReal (p z.1.toNNReal x z.2)
          ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod volume) := by
  obtain ⟨p, hp, hn, hrep⟩ := u6_regular_signed_joint_time_space_density hd ω lam Λ hΛ hω
  refine ⟨p, hp, hn, ?_⟩
  intro x α F hFm
  let μ : Measure ℝ := volume.restrict (Set.Ioi (0 : ℝ))
  let G : ℝ × Path d → ℝ × Vec d := fun z => (z.1, z.2 z.1.toNNReal)
  let q : ℝ × Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal (p z.1.toNNReal x z.2)
  have hG : Measurable G := measurable_fst.prodMk ((continuous_eval.comp
    (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))).measurable)
  have hq : Measurable q := (hp.comp (((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
    (measurable_const.prodMk measurable_snd)))).ennreal_ofReal
  have hmeasure : Measure.map G (μ.prod (K x)) = (μ.prod volume).withDensity q := by
    ext S hS
    rw [Measure.map_apply hG hS, Measure.prod_apply (hS.preimage hG),
      withDensity_apply _ hS]
    rw [← lintegral_indicator hS, lintegral_prod _ (hq.indicator hS).aemeasurable]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hmarg := Blueprint.k11_endpoint (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω)
      K hfdd t.toNNReal x
    rw [(hrep t.toNNReal (Real.toNNReal_pos.mpr ht) x).2.2] at hmarg
    have hs : MeasurableSet (Prod.mk t ⁻¹' S) := measurable_prodMk_left hS
    have he := congrArg (fun ν : Measure (Vec d) => ν (Prod.mk t ⁻¹' S)) hmarg
    rw [Measure.map_apply (measurable_pathPosition _) hs, withDensity_apply _ hs] at he
    rw [← lintegral_indicator hs] at he
    convert he using 1
    · congr 1
    · apply lintegral_congr
      intro y
      by_cases hy : (t, y) ∈ S <;> simp [q, Set.indicator, hy]
  let H : ℝ × Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (-α * z.1)) * F z
  have hH : Measurable H := ((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).measurable.ennreal_ofReal).mul hFm
  calc
    _ = ∫⁻ z, H (G z) ∂(μ.prod (K x)) := by
      change _ = ∫⁻ z, (H ∘ G) z ∂(μ.prod (K x))
      rw [lintegral_prod _ (hH.comp hG).aemeasurable]
      apply lintegral_congr
      intro t
      dsimp [H, G]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ = ∫⁻ z, H z ∂Measure.map G (μ.prod (K x)) :=
      (lintegral_map hH hG).symm
    _ = ∫⁻ z, H z * q z ∂(μ.prod volume) := by
      rw [hmeasure, lintegral_withDensity_eq_lintegral_mul _ hq hH]
      simp only [Pi.mul_apply, mul_comm]
    _ = _ := rfl

end EinsteinFull
