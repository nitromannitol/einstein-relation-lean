import EinsteinFull.Calculus.U4RegularKernelSmoothing
import EinsteinFull.Calculus.U6JointSignedKernelDensity
import EinsteinFull.Calculus.U5RegularKernelInvariance
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open EinsteinRelation EinsteinRelation.SpatialDirichlet MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

namespace EinsteinFull

/-- Discounted occupation under the supplied path law is the actual regular resolvent. -/
theorem u6_regular_signed_path_laplace
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ) :
    (∫ γ : Path d, (∫ t : ℝ in Set.Ioi 0,
      Real.exp (-s * t) * g (γ t.toNNReal)) ∂K x) =
      u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g x := by
  let S := u2RegularC0Semigroup hd ω lam Λ hΛ hω
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun f => f x
        map_add' := by intro f h; rfl
        map_smul' := by intro c f; rfl } 1 (by
          intro f
          simpa using BoundedContinuousFunction.norm_coe_le_norm f.toBCF x)
  have hm (t : ℝ) : (∫ γ : Path d, g (γ t.toNNReal) ∂K x) = S t.toNNReal g x := by
    change (∫ γ : Path d, g (pathPosition t.toNNReal γ) ∂K x) = _
    have hmap := integral_map (μ := K x) (measurable_pathPosition t.toNNReal).aemeasurable
      (f := fun y => g y) g.continuous.aestronglyMeasurable
    rw [← hmap]
    change (∫ y, g y ∂(K x).map (pathPosition t.toNNReal)) = _
    rw [Blueprint.k11_endpoint (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω)
      K hfdd t.toNNReal x]
    exact u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω _ g x
  have heval : Continuous (fun z : ℝ × Path d => z.2 z.1.toNNReal) :=
    continuous_eval.comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))
  have hi : Integrable (fun z : ℝ × Path d => Real.exp (-s * z.1) *
      g (z.2 z.1.toNNReal)) ((volume.restrict (Set.Ioi 0)).prod (K x)) := by
    apply (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const ‖g‖).comp_fst
      (K x)).mono'
      (((Real.continuous_exp.comp (continuous_const.mul continuous_fst)).mul
        (g.continuous.comp heval)).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      change ‖Real.exp (-s * z.1) * g (z.2 z.1.toNNReal)‖ ≤ Real.exp (-s * z.1) * ‖g‖
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _)
        (Real.exp_nonneg _)
  have hev : (fun t : ℝ => Real.exp (-s * t) *
      (∫ γ : Path d, g (γ t.toNNReal) ∂K x)) =
      fun t => ev (S.laplaceIntegrand s g t) := by
    funext t
    simp [hm, MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, ev]
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) *
        (∫ γ : Path d, g (γ t.toNNReal) ∂K x) := by
      rw [← integral_integral_swap hi]
      simp only [integral_const_mul]
    _ = ev (∫ t in Set.Ioi 0, S.laplaceIntegrand s g t) := by
      rw [hev]
      simpa only [Function.comp_def] using (ev.integral_comp_comm (S.integrableOn_laplaceIntegrand hs g))
    _ = ev (S.resolvent ⟨s, hs⟩ g) := by rw [S.resolvent_apply]
    _ = _ := by rw [show S.resolvent ⟨s, hs⟩ = _ from
      u2_regular_c0_semigroup_resolvent hd ω lam Λ hΛ hω ⟨s, hs⟩]; rfl

#print axioms u6_regular_signed_path_laplace

/-- Discounted joint-time density has the expected total mass at every start. -/
theorem u6_regular_signed_discounted_density_mass
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (s : ℝ) (hs : 0 < s) :
    ∃ p : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) ∧
      (∀ t x y, 0 ≤ p t x y) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ x : Vec d,
        Integrable (p t x) volume ∧ (∫ y, p t x y) = 1 ∧
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          volume.withDensity (fun y => ENNReal.ofReal (p t x y))) ∧
      ∀ x : Vec d,
        (∫⁻ y : Vec d, ∫⁻ t : ℝ in Set.Ioi 0,
          ENNReal.ofReal (Real.exp (-s * t) * p t.toNNReal x y)) =
            ENNReal.ofReal s⁻¹ := by
  obtain ⟨p, hp, hn, hrep⟩ := u6_regular_signed_joint_time_space_density hd ω lam Λ hΛ hω
  refine ⟨p, hp, hn, hrep, ?_⟩
  intro x
  let f : ℝ × Vec d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-s * z.1) * p z.1.toNNReal x z.2)
  have hfm : Measurable f := ((Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_fst)).mul
    (hp.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd)))).ennreal_ofReal
  change (∫⁻ y, ∫⁻ t, f (t, y) ∂(volume.restrict (Set.Ioi 0))) = _
  rw [← lintegral_prod (fun z : Vec d × ℝ => f (z.2, z.1))
    (hfm.comp measurable_swap).aemeasurable]
  change (∫⁻ z : Vec d × ℝ, f z.swap ∂(volume.prod (volume.restrict (Set.Ioi 0)))) = _
  rw [lintegral_prod_swap, lintegral_prod _ hfm.aemeasurable]
  have he : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      (∫⁻ y, f (t, y)) = ENNReal.ofReal (Real.exp (-s * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
    have hi := (hrep t.toNNReal ht' x).1
    have hm := (hrep t.toNNReal ht' x).2.1
    have hh := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (hn _ _))
    rw [hm] at hh
    simp only [ENNReal.ofReal_one] at hh
    simp only [f, ENNReal.ofReal_mul (Real.exp_nonneg _)]
    have hpm : Measurable (fun y => ENNReal.ofReal (p t.toNNReal x y)) :=
      (hp.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).ennreal_ofReal
    rw [lintegral_const_mul _ hpm, ← hh, mul_one]
  rw [lintegral_congr_ae he]
  have hi := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0
  have hh := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun t => Real.exp_nonneg (-s * t))
  rw [← hh, integral_exp_mul_Ioi (neg_lt_zero.mpr hs)]
  simp

#print axioms u6_regular_signed_discounted_density_mass

/-- The discounted density has a jointly measurable, integrable real representative. -/
theorem u6_regular_signed_discounted_real_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (s : ℝ) (hs : 0 < s) :
    ∃ p : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) ∧
      (∀ t x y, 0 ≤ p t x y) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ x : Vec d,
        Integrable (p t x) volume ∧ (∫ y, p t x y) = 1 ∧
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          volume.withDensity (fun y => ENNReal.ofReal (p t x y))) ∧
      ∃ r : Vec d → Vec d → ℝ, Measurable (Function.uncurry r) ∧
        (∀ x y, 0 ≤ r x y) ∧
        (∀ x y, r x y = ∫ t : ℝ in Set.Ioi 0,
          Real.exp (-s * t) * p t.toNNReal x y) ∧
        ∀ x, Integrable (r x) volume ∧ (∫ y, r x y) = s⁻¹ := by
  obtain ⟨p, hp, hn, hrep, hmass⟩ :=
    u6_regular_signed_discounted_density_mass hd ω lam Λ hΛ hω s hs
  let q : (Vec d × Vec d) × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-s * z.2) * p z.2.toNNReal z.1.1 z.1.2)
  have hq : Measurable q := ((Real.continuous_exp.measurable.comp
    (measurable_const.mul measurable_snd)).mul
    (hp.comp ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk
      ((measurable_fst.comp measurable_fst).prodMk (measurable_snd.comp measurable_fst))))).ennreal_ofReal
  let r : Vec d → Vec d → ℝ := fun x y =>
    (∫⁻ t : ℝ in Set.Ioi 0, q ((x, y), t)).toReal
  have hr : Measurable (Function.uncurry r) :=
    ENNReal.measurable_toReal.comp (hq.lintegral_prod_right' (ν := volume.restrict (Set.Ioi 0)))
  refine ⟨p, hp, hn, hrep, r, hr, fun x y => ENNReal.toReal_nonneg, ?_, ?_⟩
  · intro x y
    have hqm : Measurable (fun t => q ((x, y), t)) :=
      hq.comp (measurable_const.prodMk measurable_id)
    have he := integral_toReal (μ := volume.restrict (Set.Ioi (0 : ℝ))) hqm.aemeasurable
      (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)
    simpa only [r, q, ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) (hn _ _ _))] using he.symm
  · intro x
    have hqx : Measurable (fun y => ∫⁻ t : ℝ in Set.Ioi 0, q ((x, y), t)) :=
      (hq.lintegral_prod_right' (ν := volume.restrict (Set.Ioi 0))).comp
        (measurable_const.prodMk measurable_id)
    have hfin : (∫⁻ y, ∫⁻ t : ℝ in Set.Ioi 0, q ((x, y), t)) ≠ ∞ := by
      rw [hmass x]
      exact ENNReal.ofReal_ne_top
    have hi : Integrable (r x) volume :=
      integrable_toReal_of_lintegral_ne_top hqx.aemeasurable hfin
    refine ⟨hi, ?_⟩
    have hae := ae_lt_top hqx hfin
    have he := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun y => ENNReal.toReal_nonneg)
    have hlin : (∫⁻ y, ENNReal.ofReal (r x y)) = ENNReal.ofReal s⁻¹ := by
      rw [← hmass x]
      apply lintegral_congr_ae
      filter_upwards [hae] with y hy
      exact ENNReal.ofReal_toReal hy.ne
    rw [hlin] at he
    have he' := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_ofReal (integral_nonneg (fun y => ENNReal.toReal_nonneg))] at he'
    simpa [ENNReal.toReal_ofReal, le_of_lt hs] using he'

#print axioms u6_regular_signed_discounted_real_density

/-- The regular signed resolvent admits a jointly measurable real density. -/
theorem u6_regular_signed_resolvent_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (s : ℝ) (hs : 0 < s) :
    ∃ r : Vec d → Vec d → ℝ, Measurable (Function.uncurry r) ∧
      (∀ x y, 0 ≤ r x y) ∧ ∀ x : Vec d,
        Integrable (r x) volume ∧ (∫ y, r x y) = s⁻¹ ∧
        ∀ g : ZeroAtInftyContinuousMap (Vec d) ℝ,
          u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g x =
            ∫ y, r x y * g y := by
  obtain ⟨p, hp, hn, hrep, r, hr, hrn, hre, hrmass⟩ :=
    u6_regular_signed_discounted_real_density hd ω lam Λ hΛ hω s hs
  refine ⟨r, hr, hrn, ?_⟩
  intro x
  refine ⟨(hrmass x).1, (hrmass x).2, ?_⟩
  intro g
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : ℝ × Vec d → ℝ := fun z => Real.exp (-s * z.1) * p z.1.toNNReal x z.2
  have hF : Measurable F := ((Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_fst)).mul
    (hp.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))))
  have hFn (z : ℝ × Vec d) : 0 ≤ F z := mul_nonneg (Real.exp_nonneg _) (hn _ _ _)
  have hnorm : ∀ᵐ t ∂μ, (∫ y, ‖F (t, y)‖) = Real.exp (-s * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
    simp only [Real.norm_eq_abs, F, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hn _ _ _)),
      integral_const_mul, (hrep t.toNNReal ht' x).2.1, mul_one]
  have hi : Integrable F (μ.prod volume) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [F] using ((hrep t.toNNReal (Real.toNNReal_pos.mpr ht) x).1).const_mul (Real.exp (-s * t))
    · exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).congr (hnorm.mono fun _ h => h.symm)
  let H : ℝ × Vec d → ℝ := fun z => F z * g z.2
  have hH : Integrable H (μ.prod volume) := by
    apply (hi.mul_const ‖g‖).mono'
      ((hF.mul (g.continuous.measurable.comp measurable_snd)).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      change ‖F z * g z.2‖ ≤ F z * ‖g‖
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hFn z)]
      exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _) (hFn z)
  let S := u2RegularC0Semigroup hd ω lam Λ hΛ hω
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun f => f x
        map_add' := by intro f h; rfl
        map_smul' := by intro c f; rfl } 1 (by
          intro f
          simpa using BoundedContinuousFunction.norm_coe_le_norm f.toBCF x)
  have hkernel : ∀ᵐ t ∂μ, (∫ y, H (t, y)) = ev (S.laplaceIntegrand s g t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
    have hpmeas : Measurable (p t.toNNReal x) :=
      hp.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hh := u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω t.toNNReal g x
    rw [(hrep t.toNNReal ht' x).2.2,
      integral_withDensity_eq_integral_toReal_smul hpmeas.ennreal_ofReal
        (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top) g] at hh
    simp only [ENNReal.toReal_ofReal (hn _ _ _), smul_eq_mul] at hh
    simp only [H, F, mul_assoc, integral_const_mul,
      MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, ev]
    rw [hh]
    rfl
  calc
    _ = ev (S.resolvent ⟨s, hs⟩ g) := by
      rw [show S.resolvent ⟨s, hs⟩ = _ from
        u2_regular_c0_semigroup_resolvent hd ω lam Λ hΛ hω ⟨s, hs⟩]
      rfl
    _ = ∫ t : ℝ in Set.Ioi 0, ev (S.laplaceIntegrand s g t) := by
      rw [S.resolvent_apply]
      exact (ev.integral_comp_comm (S.integrableOn_laplaceIntegrand hs g)).symm
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ y, H (t, y) := by
      exact integral_congr_ae (hkernel.mono fun _ h => h.symm)
    _ = ∫ y, ∫ t : ℝ in Set.Ioi 0, H (t, y) := integral_integral_swap hH
    _ = ∫ y, r x y * g y := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [H, integral_mul_const, F, ← hre x y]

#print axioms u6_regular_signed_resolvent_density

private theorem u6_joint_mass_aux
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0 → Vec d → Vec d → ℝ)
    (hp : Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2))
    (hn : ∀ t x y, 0 ≤ p t x y)
    (hrep : ∀ (t : ℝ≥0), 0 < t → ∀ x : Vec d,
      Integrable (p t x) volume ∧ (∫ y, p t x y) = 1 ∧
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (p t x y))) :
    ∀ x : Vec d, (∫⁻ y : Vec d, ∫⁻ t : ℝ in Set.Ioi 0,
      ENNReal.ofReal (Real.exp (-s * t) * p t.toNNReal x y)) = ENNReal.ofReal s⁻¹ := by
  intro x
  let f : ℝ × Vec d → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-s * z.1) * p z.1.toNNReal x z.2)
  have hfm : Measurable f := ((Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_fst)).mul
    (hp.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd)))).ennreal_ofReal
  change (∫⁻ y, ∫⁻ t, f (t, y) ∂(volume.restrict (Set.Ioi 0))) = _
  rw [← lintegral_prod (fun z : Vec d × ℝ => f (z.2, z.1))
    (hfm.comp measurable_swap).aemeasurable]
  change (∫⁻ z : Vec d × ℝ, f z.swap ∂(volume.prod (volume.restrict (Set.Ioi 0)))) = _
  rw [lintegral_prod_swap, lintegral_prod _ hfm.aemeasurable]
  have he : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
      (∫⁻ y, f (t, y)) = ENNReal.ofReal (Real.exp (-s * t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
    have hi := (hrep t.toNNReal ht' x).1
    have hm := (hrep t.toNNReal ht' x).2.1
    have hh := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (hn _ _))
    rw [hm] at hh
    simp only [ENNReal.ofReal_one] at hh
    simp only [f, ENNReal.ofReal_mul (Real.exp_nonneg _)]
    have hpm : Measurable (fun y => ENNReal.ofReal (p t.toNNReal x y)) :=
      (hp.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))).ennreal_ofReal
    rw [lintegral_const_mul _ hpm, ← hh, mul_one]
  rw [lintegral_congr_ae he]
  have hi := integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0
  have hh := ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun t => Real.exp_nonneg (-s * t))
  rw [← hh, integral_exp_mul_Ioi (neg_lt_zero.mpr hs)]
  simp


private theorem u6_joint_rep_aux
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (s : ℝ) (hs : 0 < s)
    (p : ℝ≥0 → Vec d → Vec d → ℝ)
    (hp : Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2))
    (hn : ∀ t x y, 0 ≤ p t x y)
    (hrep : ∀ (t : ℝ≥0), 0 < t → ∀ x : Vec d,
      Integrable (p t x) volume ∧ (∫ y, p t x y) = 1 ∧
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (p t x y)))
    (r : Vec d → Vec d → ℝ)
    (hre : ∀ x y, r x y = ∫ t : ℝ in Set.Ioi 0,
      Real.exp (-s * t) * p t.toNNReal x y)
    (x : Vec d) (g : ZeroAtInftyContinuousMap (Vec d) ℝ) :
    u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g x = ∫ y, r x y * g y := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : ℝ × Vec d → ℝ := fun z => Real.exp (-s * z.1) * p z.1.toNNReal x z.2
  have hF : Measurable F := ((Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_fst)).mul
    (hp.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))))
  have hFn (z : ℝ × Vec d) : 0 ≤ F z := mul_nonneg (Real.exp_nonneg _) (hn _ _ _)
  have hnorm : ∀ᵐ t ∂μ, (∫ y, ‖F (t, y)‖) = Real.exp (-s * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
    simp only [Real.norm_eq_abs, F, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hn _ _ _)),
      integral_const_mul, (hrep t.toNNReal ht' x).2.1, mul_one]
  have hi : Integrable F (μ.prod volume) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [F] using ((hrep t.toNNReal (Real.toNNReal_pos.mpr ht) x).1).const_mul (Real.exp (-s * t))
    · exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).congr (hnorm.mono fun _ h => h.symm)
  let H : ℝ × Vec d → ℝ := fun z => F z * g z.2
  have hH : Integrable H (μ.prod volume) := by
    apply (hi.mul_const ‖g‖).mono'
      ((hF.mul (g.continuous.measurable.comp measurable_snd)).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      change ‖F z * g z.2‖ ≤ F z * ‖g‖
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hFn z)]
      exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _) (hFn z)
  let S := u2RegularC0Semigroup hd ω lam Λ hΛ hω
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun f => f x
        map_add' := by intro f h; rfl
        map_smul' := by intro c f; rfl } 1 (by
          intro f
          simpa using BoundedContinuousFunction.norm_coe_le_norm f.toBCF x)
  have hkernel : ∀ᵐ t ∂μ, (∫ y, H (t, y)) = ev (S.laplaceIntegrand s g t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have ht' : 0 < t.toNNReal := Real.toNNReal_pos.mpr ht
    have hpmeas : Measurable (p t.toNNReal x) :=
      hp.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hh := u2RegularC0KernelSemigroup_integral hd ω lam Λ hΛ hω t.toNNReal g x
    rw [(hrep t.toNNReal ht' x).2.2,
      integral_withDensity_eq_integral_toReal_smul hpmeas.ennreal_ofReal
        (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top) g] at hh
    simp only [ENNReal.toReal_ofReal (hn _ _ _), smul_eq_mul] at hh
    simp only [H, F, mul_assoc, integral_const_mul,
      MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, ev]
    rw [hh]
    rfl
  calc
    _ = ev (S.resolvent ⟨s, hs⟩ g) := by
      rw [show S.resolvent ⟨s, hs⟩ = _ from
        u2_regular_c0_semigroup_resolvent hd ω lam Λ hΛ hω ⟨s, hs⟩]
      rfl
    _ = ∫ t : ℝ in Set.Ioi 0, ev (S.laplaceIntegrand s g t) := by
      rw [S.resolvent_apply]
      exact (ev.integral_comp_comm (S.integrableOn_laplaceIntegrand hs g)).symm
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ y, H (t, y) := by
      exact integral_congr_ae (hkernel.mono fun _ h => h.symm)
    _ = ∫ y, ∫ t : ℝ in Set.Ioi 0, H (t, y) := integral_integral_swap hH
    _ = ∫ y, r x y * g y := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [H, integral_mul_const, F, ← hre x y]


/-- One measurable density represents the regular signed resolvent at every positive shift. -/
theorem u6_regular_signed_joint_resolvent_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ r : MarkovProcess.Semigroup.PositiveShift → Vec d → Vec d → ℝ,
      Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
        r z.1 z.2.1 z.2.2) ∧
      (∀ (s : MarkovProcess.Semigroup.PositiveShift) x y, 0 ≤ r s x y) ∧
      (∀ (s : MarkovProcess.Semigroup.PositiveShift) x, Integrable (r s x) volume ∧ ∫ y, r s x y = (s : ℝ)⁻¹) ∧
      ∀ (s : MarkovProcess.Semigroup.PositiveShift) x (g : ZeroAtInftyContinuousMap (Vec d) ℝ),
        u2RegularC0Resolvent hd ω lam Λ hΛ hω (s : ℝ) s.property g x =
          ∫ y, r s x y * g y := by
  obtain ⟨p, hp, hn, hrep⟩ := u6_regular_signed_joint_time_space_density hd ω lam Λ hΛ hω
  let q : (MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d) × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-(z.1.1 : ℝ) * z.2) * p z.2.toNNReal z.1.2.1 z.1.2.2)
  have hq : Measurable q := ((Real.continuous_exp.measurable.comp
    (((measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).neg).mul measurable_snd)).mul
    (hp.comp ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst)))))).ennreal_ofReal
  let r : MarkovProcess.Semigroup.PositiveShift → Vec d → Vec d → ℝ := fun s x y =>
    (∫⁻ t : ℝ in Set.Ioi 0, q ((s, x, y), t)).toReal
  have hr : Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
      r z.1 z.2.1 z.2.2) :=
    ENNReal.measurable_toReal.comp (hq.lintegral_prod_right' (ν := volume.restrict (Set.Ioi 0)))
  have hre (s : MarkovProcess.Semigroup.PositiveShift) (x y : Vec d) :
      r s x y = ∫ t : ℝ in Set.Ioi 0, Real.exp (-(s : ℝ) * t) * p t.toNNReal x y := by
    have hqm : Measurable (fun t => q ((s, x, y), t)) :=
      hq.comp (measurable_const.prodMk measurable_id)
    have he := integral_toReal (μ := volume.restrict (Set.Ioi (0 : ℝ))) hqm.aemeasurable
      (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)
    simpa only [r, q, ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) (hn _ _ _))] using he.symm
  refine ⟨r, hr, (fun s x y => ENNReal.toReal_nonneg), ?_, ?_⟩
  · intro s x
    have hmass := u6_joint_mass_aux hd ω lam Λ hΛ hω (s : ℝ) s.property p hp hn hrep x
    have hqx : Measurable (fun y => ∫⁻ t : ℝ in Set.Ioi 0, q ((s, x, y), t)) :=
      (hq.lintegral_prod_right' (ν := volume.restrict (Set.Ioi 0))).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hfin : (∫⁻ y, ∫⁻ t : ℝ in Set.Ioi 0, q ((s, x, y), t)) ≠ ∞ := by
      rw [hmass]
      exact ENNReal.ofReal_ne_top
    have hi : Integrable (r s x) volume := integrable_toReal_of_lintegral_ne_top hqx.aemeasurable hfin
    refine ⟨hi, ?_⟩
    have hae := ae_lt_top hqx hfin
    have he := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun y => ENNReal.toReal_nonneg)
    have hlin : (∫⁻ y, ENNReal.ofReal (r s x y)) = ENNReal.ofReal (s : ℝ)⁻¹ := by
      rw [← hmass]
      apply lintegral_congr_ae
      filter_upwards [hae] with y hy
      exact ENNReal.ofReal_toReal hy.ne
    rw [hlin] at he
    have he' := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_ofReal (integral_nonneg (fun y => ENNReal.toReal_nonneg))] at he'
    simpa [ENNReal.toReal_ofReal, le_of_lt (show 0 < (s : ℝ) from s.property)] using he'
  · intro s x g
    exact u6_joint_rep_aux hd ω lam Λ hΛ hω s s.property p hp hn hrep (r s) (hre s) x g

#print axioms u6_regular_signed_joint_resolvent_density

/-- Finite nonnegative density rows have an integrable two-step composition. -/
theorem u6_resolvent_density_composition_integrable
    {d : ℕ} (r : MarkovProcess.Semigroup.PositiveShift → Vec d → Vec d → ℝ)
    (hr : Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
      r z.1 z.2.1 z.2.2))
    (hn : ∀ s x y, 0 ≤ r s x y)
    (hmass : ∀ s x, Integrable (r s x) volume ∧ ∫ y, r s x y = (s : ℝ)⁻¹)
    (s t : MarkovProcess.Semigroup.PositiveShift) (x : Vec d) :
    Integrable (fun z : Vec d × Vec d => r s x z.1 * r t z.1 z.2)
      (volume.prod volume) := by
  let F : Vec d × Vec d → ℝ := fun z => r s x z.1 * r t z.1 z.2
  have hF : Measurable F := by
    apply Measurable.mul
    · exact hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_fst))
    · exact hr.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd))
  have hnorm : ∀ z : Vec d, (∫ y, ‖F (z, y)‖) = r s x z * (t : ℝ)⁻¹ := by
    intro z
    simp only [F, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hn _ _ _) (hn _ _ _)),
      integral_const_mul, (hmass t z).2]
  apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall fun z => (hmass t z).1.const_mul (r s x z)
  · exact ((hmass s x).1.mul_const ((t : ℝ)⁻¹)).congr
      (Filter.Eventually.of_forall fun z => (hnorm z).symm)

#print axioms u6_resolvent_density_composition_integrable

/-- The actual resolvent identity tested against C₀ functions, with its composed density. -/
theorem u6_resolvent_density_identity_test
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (r : MarkovProcess.Semigroup.PositiveShift → Vec d → Vec d → ℝ)
    (hr : Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
      r z.1 z.2.1 z.2.2))
    (hn : ∀ s x y, 0 ≤ r s x y)
    (hmass : ∀ s x, Integrable (r s x) volume ∧ ∫ y, r s x y = (s : ℝ)⁻¹)
    (hrep : ∀ (s : MarkovProcess.Semigroup.PositiveShift) x (g : ZeroAtInftyContinuousMap (Vec d) ℝ),
      u2RegularC0Resolvent hd ω lam Λ hΛ hω (s : ℝ) s.property g x =
        ∫ y, r s x y * g y)
    (s t : MarkovProcess.Semigroup.PositiveShift) (x : Vec d)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ) :
    (∫ y, r s x y * g y) - (∫ y, r t x y * g y) =
      ((t : ℝ) - (s : ℝ)) *
        ∫ y, (∫ z, r s x z * r t z y) * g y := by
  let F : Vec d × Vec d → ℝ := fun z => r s x z.1 * r t z.1 z.2
  have hF : Measurable F :=
    (hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_fst))).mul
      (hr.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))
  have hFn (z : Vec d × Vec d) : 0 ≤ F z := mul_nonneg (hn _ _ _) (hn _ _ _)
  have hi : Integrable F (volume.prod volume) :=
    u6_resolvent_density_composition_integrable r hr hn hmass s t x
  let H : Vec d × Vec d → ℝ := fun z => F z * g z.2
  have hH : Integrable H (volume.prod volume) := by
    apply (hi.mul_const ‖g‖).mono'
      ((hF.mul (g.continuous.measurable.comp measurable_snd)).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      change ‖F z * g z.2‖ ≤ F z * ‖g‖
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hFn z)]
      exact mul_le_mul_of_nonneg_left (BoundedContinuousFunction.norm_coe_le_norm g.toBCF _) (hFn z)
  have hcomp : (∫ z, r s x z *
      u2RegularC0Resolvent hd ω lam Λ hΛ hω (t : ℝ) t.property g z) =
      ∫ y, (∫ z, r s x z * r t z y) * g y := by
    calc
      _ = ∫ z, ∫ y, H (z, y) := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hrep t z g, ← integral_const_mul]
        simp only [H, F, mul_assoc]
      _ = ∫ y, ∫ z, H (z, y) := integral_integral_swap hH
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with y
        simp only [H, F, integral_mul_const]
  have he := congrArg (fun f : ZeroAtInftyContinuousMap (Vec d) ℝ => f x)
    (u2_regular_c0_resolvent_identity hd ω lam Λ hΛ hω (s : ℝ) (t : ℝ)
      s.property t.property g)
  simp only [ZeroAtInftyContinuousMap.sub_apply, ZeroAtInftyContinuousMap.smul_apply,
    smul_eq_mul] at he
  rw [hrep s x g, hrep t x g, hrep s x
    (u2RegularC0Resolvent hd ω lam Λ hΛ hω (t : ℝ) t.property g), hcomp] at he
  exact he

#print axioms u6_resolvent_density_identity_test

/-- Integrable nonnegative densities are determined by their C₀ test integrals. -/
theorem u6_nonnegative_density_eq_of_c0_tests {d : ℕ} (f h : Vec d → ℝ)
    (hf : Integrable f volume) (hh : Integrable h volume)
    (hfn : ∀ y, 0 ≤ f y) (hhn : ∀ y, 0 ≤ h y)
    (htest : ∀ g : ZeroAtInftyContinuousMap (Vec d) ℝ,
      (∫ y, f y * g y) = ∫ y, h y * g y) : f =ᵐ[volume] h := by
  have hfi : (∫⁻ y, ENNReal.ofReal (f y)) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hf (ae_of_all _ hfn)]
    exact ENNReal.ofReal_ne_top
  have hhi : (∫⁻ y, ENNReal.ofReal (h y)) ≠ ∞ := by
    rw [← ofReal_integral_eq_lintegral_ofReal hh (ae_of_all _ hhn)]
    exact ENNReal.ofReal_ne_top
  let μ := (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal (f y))
  let ν := (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal (h y))
  let : IsFiniteMeasure μ := isFiniteMeasure_withDensity hfi
  let : IsFiniteMeasure ν := isFiniteMeasure_withDensity hhi
  have heq : μ = ν := by
    apply Measure.ext_of_integral_eq_on_compactlySupported
    intro g
    let g₀ : ZeroAtInftyContinuousMap (Vec d) ℝ :=
      ⟨⟨g, g.continuous⟩, g.hasCompactSupport.is_zero_at_infty⟩
    change (∫ y, g y ∂μ) = ∫ y, g y ∂ν
    rw [show μ = volume.withDensity (fun y => ENNReal.ofReal (f y)) from rfl,
      show ν = volume.withDensity (fun y => ENNReal.ofReal (h y)) from rfl,
      integral_withDensity_eq_integral_toReal_smul₀ hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (ae_of_all _ fun y => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul₀ hh.aestronglyMeasurable.aemeasurable.ennreal_ofReal
        (ae_of_all _ fun y => ENNReal.ofReal_lt_top)]
    simpa only [ENNReal.toReal_ofReal (hfn _), ENNReal.toReal_ofReal (hhn _), smul_eq_mul, g₀, ZeroAtInftyContinuousMap.coe_mk]
      using htest g₀
  have hae := (withDensity_eq_iff_of_sigmaFinite
    hf.aestronglyMeasurable.aemeasurable.ennreal_ofReal
    hh.aestronglyMeasurable.aemeasurable.ennreal_ofReal).mp heq
  filter_upwards [hae] with y hy
  have he := congrArg ENNReal.toReal hy
  simpa only [ENNReal.toReal_ofReal (hfn y), ENNReal.toReal_ofReal (hhn y)] using he

/-- The joint resolvent density satisfies the pointwise-shift resolvent identity almost everywhere. -/
theorem u6_regular_signed_resolvent_density_identity
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ r : MarkovProcess.Semigroup.PositiveShift → Vec d → Vec d → ℝ,
      Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
        r z.1 z.2.1 z.2.2) ∧
      (∀ (s : MarkovProcess.Semigroup.PositiveShift) (x y : Vec d), 0 ≤ r s x y) ∧
      (∀ (s : MarkovProcess.Semigroup.PositiveShift) (x : Vec d), Integrable (r s x) volume ∧ ∫ y, r s x y = (s : ℝ)⁻¹) ∧
      (∀ (s : MarkovProcess.Semigroup.PositiveShift) (x : Vec d) (g : ZeroAtInftyContinuousMap (Vec d) ℝ),
        u2RegularC0Resolvent hd ω lam Λ hΛ hω (s : ℝ) s.property g x =
          ∫ y, r s x y * g y) ∧
      ∀ (s t : MarkovProcess.Semigroup.PositiveShift) (x : Vec d), ∀ᵐ y ∂(volume : Measure (Vec d)),
        r s x y - r t x y = ((t : ℝ) - (s : ℝ)) *
          ∫ z, r s x z * r t z y := by
  obtain ⟨r, hr, hn, hm, hrep⟩ := u6_regular_signed_joint_resolvent_density hd ω lam Λ hΛ hω
  refine ⟨r, hr, hn, hm, hrep, ?_⟩
  intro s t x
  by_cases hst : s = t
  · subst t
    filter_upwards with y
    simp
  let q : Vec d → ℝ := fun y => ∫ z, r s x z * r t z y
  have hq : Integrable q volume :=
    (u6_resolvent_density_composition_integrable r hr hn hm s t x).integral_prod_right
  have hqn : ∀ y, 0 ≤ q y := fun y => integral_nonneg fun z => mul_nonneg (hn _ _ _) (hn _ _ _)
  let c : ℝ := (t : ℝ) - (s : ℝ)
  let a : ℝ := max (-c) 0
  let b : ℝ := max c 0
  have ha : 0 ≤ a := le_max_right _ _
  have hb : 0 ≤ b := le_max_right _ _
  have hba : b - a = c := by
    dsimp [a, b]
    by_cases hc : 0 ≤ c
    · rw [max_eq_left hc, max_eq_right (neg_nonpos.mpr hc)]; ring
    · have hc' : c ≤ 0 := le_of_not_ge hc
      rw [max_eq_right hc', max_eq_left (neg_nonneg.mpr hc')]; ring
  let f : Vec d → ℝ := fun y => r s x y + a * q y
  let h : Vec d → ℝ := fun y => r t x y + b * q y
  have hf : Integrable f volume := (hm s x).1.add (hq.const_mul a)
  have hh : Integrable h volume := (hm t x).1.add (hq.const_mul b)
  have hfn : ∀ y, 0 ≤ f y := fun y => add_nonneg (hn _ _ _) (mul_nonneg ha (hqn y))
  have hhn : ∀ y, 0 ≤ h y := fun y => add_nonneg (hn _ _ _) (mul_nonneg hb (hqn y))
  have htest : ∀ g : ZeroAtInftyContinuousMap (Vec d) ℝ,
      (∫ y, f y * g y) = ∫ y, h y * g y := by
    intro g
    have hbound : ∀ᵐ y ∂(volume : Measure (Vec d)), ‖g y‖ ≤ ‖g‖ :=
      ae_of_all _ fun y => BoundedContinuousFunction.norm_coe_le_norm g.toBCF y
    have hs : Integrable (fun y => r s x y * g y) volume :=
      (hm s x).1.mul_bdd g.continuous.aestronglyMeasurable hbound
    have ht : Integrable (fun y => r t x y * g y) volume :=
      (hm t x).1.mul_bdd g.continuous.aestronglyMeasurable hbound
    have hqg : Integrable (fun y => q y * g y) volume :=
      hq.mul_bdd g.continuous.aestronglyMeasurable hbound
    have he := u6_resolvent_density_identity_test hd ω lam Λ hΛ hω r hr hn hm hrep s t x g
    change (∫ y, r s x y * g y) - (∫ y, r t x y * g y) = c * (∫ y, q y * g y) at he
    simp only [f, h, add_mul, mul_assoc]
    rw [integral_add hs (hqg.const_mul a), integral_add ht (hqg.const_mul b),
      integral_const_mul, integral_const_mul]
    rw [← hba] at he
    linarith
  have heq := u6_nonnegative_density_eq_of_c0_tests f h hf hh hfn hhn htest
  filter_upwards [heq] with y hy
  change r s x y + a * q y = r t x y + b * q y at hy
  change r s x y - r t x y = c * q y
  rw [← hba]
  nlinarith

#print axioms u6_nonnegative_density_eq_of_c0_tests
#print axioms u6_regular_signed_resolvent_density_identity

/-- The joint resolvent density transported to the signed physical measure. -/
theorem u6_regular_signed_physical_resolvent_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ r : MarkovProcess.Semigroup.PositiveShift → Vec d → Vec d → ℝ,
      Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
        r z.1 z.2.1 z.2.2) ∧
      (∀ s x y, 0 ≤ r s x y) ∧
      (∀ s x, Integrable (r s x) (physicalReversibleMeasure ω hd lam) ∧
        ∫ y, r s x y ∂physicalReversibleMeasure ω hd lam = (s : ℝ)⁻¹) ∧
      ∀ (s : MarkovProcess.Semigroup.PositiveShift) x (g : ZeroAtInftyContinuousMap (Vec d) ℝ),
        u2RegularC0Resolvent hd ω lam Λ hΛ hω (s : ℝ) s.property g x =
          ∫ y, r s x y * g y ∂physicalReversibleMeasure ω hd lam := by
  obtain ⟨q, hq, hqn, hqm, hqr⟩ :=
    u6_regular_signed_joint_resolvent_density hd ω lam Λ hΛ hω
  let w := sourcePhysicalDensity ω hd lam
  have hw : Continuous w := continuousSourcePhysicalDensity ω hd lam
  have hwp (y : Vec d) : 0 < w y := positiveSourcePhysicalDensity ω hd lam y
  let r := fun s x y => q s x y / w y
  have hr : Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
      r z.1 z.2.1 z.2.2) := hq.div (hw.measurable.comp (measurable_snd.comp measurable_snd))
  have hn : ∀ s x y, 0 ≤ r s x y := fun s x y => div_nonneg (hqn s x y) (hwp y).le
  have hmeasure (s : MarkovProcess.Semigroup.PositiveShift) (x : Vec d) :
      (physicalReversibleMeasure ω hd lam).withDensity (fun y => ENNReal.ofReal (r s x y)) =
        (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal (q s x y)) := by
    change (volume.withDensity (fun y => ENNReal.ofReal (w y))).withDensity _ = _
    have hrx : Measurable (r s x) := hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    rw [← withDensity_mul volume hw.measurable.ennreal_ofReal hrx.ennreal_ofReal]
    congr 1
    funext y
    simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (hwp y).le]
    congr 1
    dsimp [r]
    field_simp [ne_of_gt (hwp y)]
  refine ⟨r, hr, hn, ?_, ?_⟩
  · intro s x
    have hlin : (∫⁻ y, ENNReal.ofReal (r s x y) ∂physicalReversibleMeasure ω hd lam) =
        ENNReal.ofReal (s : ℝ)⁻¹ := by
      have he := congrArg (fun μ : Measure (Vec d) => μ Set.univ) (hmeasure s x)
      simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at he
      rw [he, ← ofReal_integral_eq_lintegral_ofReal (hqm s x).1 (ae_of_all _ (hqn s x)), (hqm s x).2]
    have hrx : Measurable (r s x) := hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hi : Integrable (r s x) (physicalReversibleMeasure ω hd lam) := by
      have h := integrable_toReal_of_lintegral_ne_top hrx.ennreal_ofReal.aemeasurable (by rw [hlin]; exact ENNReal.ofReal_ne_top)
      simpa only [ENNReal.toReal_ofReal (hn s x _)] using h
    refine ⟨hi, ?_⟩
    have he := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (hn s x))
    rw [hlin] at he
    have he' := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (hn s x)),
      ENNReal.toReal_ofReal (inv_nonneg.mpr s.property.le)] using he'
  · intro s x g
    rw [hqr s x g]
    have hrx : Measurable (r s x) := hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hqx : Measurable (q s x) := hq.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have he := congrArg (fun μ : Measure (Vec d) => ∫ y, g y ∂μ) (hmeasure s x)
    rw [integral_withDensity_eq_integral_toReal_smul hrx.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul hqx.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at he
    simpa only [ENNReal.toReal_ofReal (hn s x _), ENNReal.toReal_ofReal (hqn s x _), smul_eq_mul] using he.symm

#print axioms u6_regular_signed_physical_resolvent_density

/-- Any jointly measurable density of the actual kernel inherits detailed balance. -/
theorem u6_regular_kernel_density_symmetric
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (p : Vec d → Vec d → ℝ) (hp : Measurable (Function.uncurry p))
    (hn : ∀ x y, 0 ≤ p x y)
    (hr : ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
      (physicalReversibleMeasure ω hd lam).withDensity (fun y => ENNReal.ofReal (p x y))) :
    ∀ᵐ z ∂(physicalReversibleMeasure ω hd lam).prod
      (physicalReversibleMeasure ω hd lam), p z.1 z.2 = p z.2 z.1 := by
  let μ := physicalReversibleMeasure ω hd lam
  let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  let f : Vec d × Vec d → ℝ≥0∞ := fun q => ENNReal.ofReal (p q.1 q.2)
  let g : Vec d × Vec d → ℝ≥0∞ := fun q => ENNReal.ofReal (p q.2 q.1)
  have hf : Measurable f := hp.ennreal_ofReal
  have hg : Measurable g := hf.comp measurable_swap
  have hrect (A B : Set (Vec d)) (hA : MeasurableSet A) (hB : MeasurableSet B) :
      (μ.prod μ).withDensity f (A ×ˢ B) = (μ.prod μ).withDensity g (A ×ˢ B) := by
    rw [withDensity_apply _ (hA.prod hB), withDensity_apply _ (hA.prod hB),
      setLIntegral_prod _ hf.aemeasurable.restrict,
      setLIntegral_prod_symm _ hg.aemeasurable.restrict]
    have h := u5_regular_kernel_measurable_rectangles hd ω lam Λ hΛ hω t A B hA hB
    change (∫⁻ x in A, K x B ∂μ) = ∫⁻ y in B, K y A ∂μ at h
    simp_rw [show ∀ x, K x = μ.withDensity (fun y => ENNReal.ofReal (p x y)) from hr,
      withDensity_apply _ hA, withDensity_apply _ hB] at h
    simpa only [f, g] using h
  have heq : (μ.prod μ).withDensity f = (μ.prod μ).withDensity g := by
    apply Measure.ext_of_iUnion_eq_univ (s := fun n => spanningSets μ n ×ˢ Set.univ)
    · ext q
      simp only [Set.mem_iUnion, Set.mem_prod, Set.mem_univ, and_true, iff_true]
      exact Set.mem_iUnion.mp (iUnion_spanningSets μ ▸ Set.mem_univ q.1)
    · intro n
      let S := spanningSets μ n
      have hS : MeasurableSet S := measurableSet_spanningSets μ n
      have hfinite : (μ.prod μ).withDensity f (S ×ˢ Set.univ) < ∞ := by
        rw [withDensity_apply _ (hS.prod MeasurableSet.univ),
          setLIntegral_prod _ hf.aemeasurable.restrict]
        have hval (x : Vec d) : (∫⁻ y, f (x, y) ∂μ) = 1 := by
          have h := congrArg (fun m : Measure (Vec d) => m Set.univ) (hr x)
          rw [u2_regular_kernel_conservative] at h
          simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, f] using h.symm
        simp only [Measure.restrict_univ, hval, lintegral_const, one_mul, Measure.restrict_apply_univ]
        exact measure_spanningSets_lt_top μ n
      let : IsFiniteMeasure (((μ.prod μ).withDensity f).restrict (S ×ˢ Set.univ)) :=
        ⟨by simpa using hfinite⟩
      apply Measure.ext_prod
      intro A B hA hB
      rw [Measure.restrict_apply (hA.prod hB), Measure.restrict_apply (hA.prod hB)]
      rw [show (A ×ˢ B) ∩ (S ×ˢ Set.univ) = (A ∩ S) ×ˢ B by ext q; simp [and_assoc, and_comm, and_left_comm]]
      exact hrect (A ∩ S) B (hA.inter hS) hB
  have hae := (withDensity_eq_iff_of_sigmaFinite hf.aemeasurable hg.aemeasurable).mp heq
  filter_upwards [hae] with q hq
  simpa only [f, g, ENNReal.toReal_ofReal (hn _ _)] using congrArg ENNReal.toReal hq

#print axioms u6_regular_kernel_density_symmetric

/-- The joint resolvent density retains its discounted transition-density formula. -/
theorem u6_regular_signed_joint_resolvent_time_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ p : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) ∧
      (∀ t x y, 0 ≤ p t x y) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ x : Vec d,
        Integrable (p t x) volume ∧ (∫ y, p t x y) = 1 ∧
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          volume.withDensity (fun y => ENNReal.ofReal (p t x y))) ∧
      ∃ r : MarkovProcess.Semigroup.PositiveShift → Vec d → Vec d → ℝ,
        Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
          r z.1 z.2.1 z.2.2) ∧
        (∀ s x y, 0 ≤ r s x y) ∧
        (∀ s x y, r s x y = ∫ t : ℝ in Set.Ioi 0,
          Real.exp (-(s : ℝ) * t) * p t.toNNReal x y) ∧
        (∀ s x, Integrable (r s x) volume ∧ ∫ y, r s x y = (s : ℝ)⁻¹) ∧
        ∀ (s : MarkovProcess.Semigroup.PositiveShift) x (g : ZeroAtInftyContinuousMap (Vec d) ℝ),
          u2RegularC0Resolvent hd ω lam Λ hΛ hω (s : ℝ) s.property g x =
            ∫ y, r s x y * g y := by
  obtain ⟨p, hp, hn, hrep⟩ := u6_regular_signed_joint_time_space_density hd ω lam Λ hΛ hω
  let q : (MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d) × ℝ → ℝ≥0∞ := fun z =>
    ENNReal.ofReal (Real.exp (-(z.1.1 : ℝ) * z.2) * p z.2.toNNReal z.1.2.1 z.1.2.2)
  have hq : Measurable q := ((Real.continuous_exp.measurable.comp
    (((measurable_subtype_coe.comp (measurable_fst.comp measurable_fst)).neg).mul measurable_snd)).mul
    (hp.comp ((continuous_real_toNNReal.measurable.comp measurable_snd).prodMk
      ((measurable_fst.comp (measurable_snd.comp measurable_fst)).prodMk
        (measurable_snd.comp (measurable_snd.comp measurable_fst)))))).ennreal_ofReal
  let r : MarkovProcess.Semigroup.PositiveShift → Vec d → Vec d → ℝ := fun s x y =>
    (∫⁻ t : ℝ in Set.Ioi 0, q ((s, x, y), t)).toReal
  have hr : Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
      r z.1 z.2.1 z.2.2) :=
    ENNReal.measurable_toReal.comp (hq.lintegral_prod_right' (ν := volume.restrict (Set.Ioi 0)))
  have hre (s : MarkovProcess.Semigroup.PositiveShift) (x y : Vec d) :
      r s x y = ∫ t : ℝ in Set.Ioi 0, Real.exp (-(s : ℝ) * t) * p t.toNNReal x y := by
    have hqm : Measurable (fun t => q ((s, x, y), t)) :=
      hq.comp (measurable_const.prodMk measurable_id)
    have he := integral_toReal (μ := volume.restrict (Set.Ioi (0 : ℝ))) hqm.aemeasurable
      (Filter.Eventually.of_forall fun t => ENNReal.ofReal_lt_top)
    simpa only [r, q, ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) (hn _ _ _))] using he.symm
  refine ⟨p, hp, hn, hrep, r, hr, (fun s x y => ENNReal.toReal_nonneg), hre, ?_, ?_⟩
  · intro s x
    have hmass := u6_joint_mass_aux hd ω lam Λ hΛ hω (s : ℝ) s.property p hp hn hrep x
    have hqx : Measurable (fun y => ∫⁻ t : ℝ in Set.Ioi 0, q ((s, x, y), t)) :=
      (hq.lintegral_prod_right' (ν := volume.restrict (Set.Ioi 0))).comp
        (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hfin : (∫⁻ y, ∫⁻ t : ℝ in Set.Ioi 0, q ((s, x, y), t)) ≠ ∞ := by
      rw [hmass]
      exact ENNReal.ofReal_ne_top
    have hi : Integrable (r s x) volume := integrable_toReal_of_lintegral_ne_top hqx.aemeasurable hfin
    refine ⟨hi, ?_⟩
    have hae := ae_lt_top hqx hfin
    have he := ofReal_integral_eq_lintegral_ofReal hi
      (Filter.Eventually.of_forall fun y => ENNReal.toReal_nonneg)
    have hlin : (∫⁻ y, ENNReal.ofReal (r s x y)) = ENNReal.ofReal (s : ℝ)⁻¹ := by
      rw [← hmass]
      apply lintegral_congr_ae
      filter_upwards [hae] with y hy
      exact ENNReal.ofReal_toReal hy.ne
    rw [hlin] at he
    have he' := congrArg ENNReal.toReal he
    rw [ENNReal.toReal_ofReal (integral_nonneg (fun y => ENNReal.toReal_nonneg))] at he'
    simpa [ENNReal.toReal_ofReal, le_of_lt (show 0 < (s : ℝ) from s.property)] using he'
  · intro s x g
    exact u6_joint_rep_aux hd ω lam Λ hΛ hω s s.property p hp hn hrep (r s) (hre s) x g


#print axioms u6_regular_signed_joint_resolvent_time_density


/-- The signed Green kernel is symmetric for the physical reversible measure. -/
theorem u6_regular_signed_reversible_green_kernel
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ r : MarkovProcess.Semigroup.PositiveShift → Vec d → Vec d → ℝ,
      Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
        r z.1 z.2.1 z.2.2) ∧
      (∀ (s : MarkovProcess.Semigroup.PositiveShift) (x y : Vec d), 0 ≤ r s x y) ∧
      (∀ (s : MarkovProcess.Semigroup.PositiveShift) (x : Vec d),
        Integrable (r s x) (physicalReversibleMeasure ω hd lam) ∧
        ∫ y, r s x y ∂physicalReversibleMeasure ω hd lam = (s : ℝ)⁻¹) ∧
      (∀ (s : MarkovProcess.Semigroup.PositiveShift) (x : Vec d)
          (g : ZeroAtInftyContinuousMap (Vec d) ℝ),
        u2RegularC0Resolvent hd ω lam Λ hΛ hω (s : ℝ) s.property g x =
          ∫ y, r s x y * g y ∂physicalReversibleMeasure ω hd lam) ∧
      ∀ s : MarkovProcess.Semigroup.PositiveShift,
        ∀ᵐ z ∂(physicalReversibleMeasure ω hd lam).prod
          (physicalReversibleMeasure ω hd lam), r s z.1 z.2 = r s z.2 z.1 := by
  obtain ⟨p, hp, hp0, hptime, q, hq, hqn, hqtime, hqm, hqr⟩ :=
    u6_regular_signed_joint_resolvent_time_density hd ω lam Λ hΛ hω
  let w := sourcePhysicalDensity ω hd lam
  have hw : Continuous w := continuousSourcePhysicalDensity ω hd lam
  have hwp (y : Vec d) : 0 < w y := positiveSourcePhysicalDensity ω hd lam y
  let r := fun s x y => q s x y / w y
  have hr : Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
      r z.1 z.2.1 z.2.2) := hq.div (hw.measurable.comp (measurable_snd.comp measurable_snd))
  have hn : ∀ s x y, 0 ≤ r s x y := fun s x y => div_nonneg (hqn s x y) (hwp y).le
  have hmeasure (s : MarkovProcess.Semigroup.PositiveShift) (x : Vec d) :
      (physicalReversibleMeasure ω hd lam).withDensity (fun y => ENNReal.ofReal (r s x y)) =
        (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal (q s x y)) := by
    change (volume.withDensity (fun y => ENNReal.ofReal (w y))).withDensity _ = _
    have hrx : Measurable (r s x) := hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    rw [← withDensity_mul volume hw.measurable.ennreal_ofReal hrx.ennreal_ofReal]
    congr 1
    funext y
    simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (hwp y).le]
    congr 1
    dsimp [r]
    field_simp [ne_of_gt (hwp y)]
  refine ⟨r, hr, hn, ?_, ?_, ?_⟩
  · intro s x
    have hlin : (∫⁻ y, ENNReal.ofReal (r s x y) ∂physicalReversibleMeasure ω hd lam) =
        ENNReal.ofReal (s : ℝ)⁻¹ := by
      have he := congrArg (fun μ : Measure (Vec d) => μ Set.univ) (hmeasure s x)
      simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at he
      rw [he, ← ofReal_integral_eq_lintegral_ofReal (hqm s x).1 (ae_of_all _ (hqn s x)), (hqm s x).2]
    have hrx : Measurable (r s x) := hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hi : Integrable (r s x) (physicalReversibleMeasure ω hd lam) := by
      have h := integrable_toReal_of_lintegral_ne_top hrx.ennreal_ofReal.aemeasurable (by rw [hlin]; exact ENNReal.ofReal_ne_top)
      simpa only [ENNReal.toReal_ofReal (hn s x _)] using h
    refine ⟨hi, ?_⟩
    have he := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (hn s x))
    rw [hlin] at he
    have he' := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (hn s x)),
      ENNReal.toReal_ofReal (inv_nonneg.mpr s.property.le)] using he'
  · intro s x g
    rw [hqr s x g]
    have hrx : Measurable (r s x) := hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hqx : Measurable (q s x) := hq.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have he := congrArg (fun μ : Measure (Vec d) => ∫ y, g y ∂μ) (hmeasure s x)
    rw [integral_withDensity_eq_integral_toReal_smul hrx.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul hqx.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at he
    simpa only [ENNReal.toReal_ofReal (hn s x _), ENNReal.toReal_ofReal (hqn s x _), smul_eq_mul] using he.symm

  · intro s
    let μ := physicalReversibleMeasure ω hd lam
    let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
    let P : ℝ × (Vec d × Vec d) → ℝ := fun z => p z.1.toNNReal z.2.1 z.2.2 / w z.2.2
    have hP : Measurable P := (hp.comp
      ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
        ((measurable_fst.comp measurable_snd).prodMk (measurable_snd.comp measurable_snd)))).div
      (hw.measurable.comp (measurable_snd.comp measurable_snd))
    have hPs : Measurable (fun z : ℝ × (Vec d × Vec d) => P (z.1, z.2.swap)) :=
      hP.comp (measurable_fst.prodMk (measurable_swap.comp measurable_snd))
    have htime (t : ℝ≥0) (ht : 0 < t) :
        ∀ᵐ z ∂μ.prod μ, p t z.1 z.2 / w z.2 = p t z.2 z.1 / w z.1 := by
      let a : Vec d → Vec d → ℝ := fun x y => p t x y / w y
      have ha : Measurable (Function.uncurry a) :=
        (hp.comp (measurable_const.prodMk measurable_id)).div (hw.measurable.comp measurable_snd)
      have han (x y : Vec d) : 0 ≤ a x y := div_nonneg (hp0 t x y) (hwp y).le
      have har (x : Vec d) : u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          μ.withDensity (fun y => ENNReal.ofReal (a x y)) := by
        rw [(hptime t ht x).2.2]
        change volume.withDensity (fun y => ENNReal.ofReal (p t x y)) =
          (volume.withDensity (fun y => ENNReal.ofReal (w y))).withDensity _
        have hax : Measurable (a x) := ha.comp (measurable_const.prodMk measurable_id)
        rw [← withDensity_mul volume hw.measurable.ennreal_ofReal hax.ennreal_ofReal]
        congr 1
        funext y
        simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (hwp y).le]
        congr 1
        dsimp [a]
        field_simp [ne_of_gt (hwp y)]
      exact u6_regular_kernel_density_symmetric hd ω lam Λ hΛ hω t a ha han har
    have hts : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))),
        ∀ᵐ z ∂μ.prod μ, P (t, z) = P (t, z.swap) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact htime t.toNNReal (Real.toNNReal_pos.mpr ht)
    have hz := (Measure.ae_ae_comm (p := fun t z => P (t, z) = P (t, z.swap))
      (measurableSet_eq_fun hP hPs)).mp hts
    filter_upwards [hz] with z hz
    change q s z.1 z.2 / w z.2 = q s z.2 z.1 / w z.1
    rw [hqtime s z.1 z.2, hqtime s z.2 z.1, ← integral_div, ← integral_div]
    apply integral_congr_ae
    filter_upwards [hz] with t ht
    change p t.toNNReal z.1 z.2 / w z.2 = p t.toNNReal z.2 z.1 / w z.1 at ht
    rw [mul_div_assoc, mul_div_assoc, ht]

#print axioms u6_regular_signed_reversible_green_kernel


/-- The discounted action of a bounded measurable observable is continuous. -/
theorem u6_regular_signed_discounted_bounded_observable_continuous
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (s : ℝ) (hs : 0 < s) (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ y, |g y| ≤ B) :
    Continuous (fun x : Vec d => ∫ t : ℝ in Set.Ioi 0,
      Real.exp (-s * t) * (∫ y, g y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t.toNNReal x)) ∧
    ∀ x : Vec d, |∫ t : ℝ in Set.Ioi 0,
      Real.exp (-s * t) * (∫ y, g y ∂
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t.toNNReal x)| ≤ B / s := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let κ : Kernel (ℝ≥0 × Vec d) (Vec d) := ⟨fun p => P p.1 p.2, P.measurable_toMeasure⟩
  let : IsMarkovKernel κ := ⟨fun p => ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω p.1 p.2⟩⟩
  have hm : Measurable (fun p : ℝ≥0 × Vec d => ∫ y, g y ∂κ p) :=
    hg.stronglyMeasurable.integral_kernel.measurable
  have hb (t : ℝ) (x : Vec d) : |∫ y, g y ∂P t.toNNReal x| ≤ B := by
    change |∫ y, g y ∂κ (t.toNNReal, x)| ≤ B
    have h := norm_integral_le_of_norm_le_const (μ := κ (t.toNNReal, x)) (f := g) (C := ‖B‖)
      (Filter.Eventually.of_forall fun y => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg hB] using hbound y)
    simpa only [Real.norm_eq_abs, abs_of_nonneg hB, probReal_univ, mul_one] using h
  let F : Vec d → ℝ → ℝ := fun x t => Real.exp (-s * t) * (∫ y, g y ∂P t.toNNReal x)
  let bound : ℝ → ℝ := fun t => Real.exp (-s * t) * B
  have hi : Integrable bound (volume.restrict (Set.Ioi 0)) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const B
  have hdom (x : Vec d) : ∀ᵐ t ∂(volume.restrict (Set.Ioi (0 : ℝ))), ‖F x t‖ ≤ bound t :=
    Filter.Eventually.of_forall fun t => by
      simp only [F, bound, norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_left (hb t x) (Real.exp_nonneg _)
  constructor
  · change Continuous (fun x => ∫ t, F x t ∂(volume.restrict (Set.Ioi 0)))
    apply continuous_of_dominated (bound := bound) ?_ hdom hi ?_
    · intro x
      exact ((Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
        (hm.comp (measurable_real_toNNReal.prodMk measurable_const))).aestronglyMeasurable
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      exact continuous_const.mul (u4_regular_signed_kernel_strongFeller hd ω lam Λ hΛ hω
        t.toNNReal (Real.toNNReal_pos.mpr ht) g hg B hbound)
  · intro x
    have h := norm_integral_le_of_norm_le hi (hdom x)
    change ‖∫ t, F x t ∂(volume.restrict (Set.Ioi 0))‖ ≤ _ at h
    have he : (∫ t, bound t ∂(volume.restrict (Set.Ioi 0))) = B / s := by
      dsimp [bound]
      rw [integral_mul_const, integral_exp_mul_Ioi (neg_lt_zero.mpr hs)]
      simp [div_eq_mul_inv, mul_comm]
    rw [he] at h
    simpa only [F, Real.norm_eq_abs] using h

#print axioms u6_regular_signed_discounted_bounded_observable_continuous

/-- The physical Green rows have exact variation under a change of positive shift. -/
theorem u6_regular_signed_green_shift_L1_variation
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ r : MarkovProcess.Semigroup.PositiveShift → Vec d → Vec d → ℝ,
      Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
        r z.1 z.2.1 z.2.2) ∧
      (∀ (s : MarkovProcess.Semigroup.PositiveShift) (x y : Vec d), 0 ≤ r s x y) ∧
      (∀ (s : MarkovProcess.Semigroup.PositiveShift) (x : Vec d),
        Integrable (r s x) (physicalReversibleMeasure ω hd lam) ∧
        ∫ y, r s x y ∂physicalReversibleMeasure ω hd lam = (s : ℝ)⁻¹) ∧
      (∀ (s : MarkovProcess.Semigroup.PositiveShift) (x : Vec d)
        (g : ZeroAtInftyContinuousMap (Vec d) ℝ),
        u2RegularC0Resolvent hd ω lam Λ hΛ hω (s : ℝ) s.property g x =
          ∫ y, r s x y * g y ∂physicalReversibleMeasure ω hd lam) ∧
      ∀ (s t : MarkovProcess.Semigroup.PositiveShift) (x : Vec d),
        (∫ y, |r s x y - r t x y| ∂physicalReversibleMeasure ω hd lam) =
          |(s : ℝ)⁻¹ - (t : ℝ)⁻¹| := by
  obtain ⟨q, hq, hqn, hqm, hqr, hident⟩ :=
    u6_regular_signed_resolvent_density_identity hd ω lam Λ hΛ hω
  let w := sourcePhysicalDensity ω hd lam
  have hw : Continuous w := continuousSourcePhysicalDensity ω hd lam
  have hwp (y : Vec d) : 0 < w y := positiveSourcePhysicalDensity ω hd lam y
  let r := fun s x y => q s x y / w y
  have hr : Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
      r z.1 z.2.1 z.2.2) := hq.div (hw.measurable.comp (measurable_snd.comp measurable_snd))
  have hn : ∀ s x y, 0 ≤ r s x y := fun s x y => div_nonneg (hqn s x y) (hwp y).le
  have hmeasure (s : MarkovProcess.Semigroup.PositiveShift) (x : Vec d) :
      (physicalReversibleMeasure ω hd lam).withDensity (fun y => ENNReal.ofReal (r s x y)) =
        (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal (q s x y)) := by
    change (volume.withDensity (fun y => ENNReal.ofReal (w y))).withDensity _ = _
    have hrx : Measurable (r s x) := hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    rw [← withDensity_mul volume hw.measurable.ennreal_ofReal hrx.ennreal_ofReal]
    congr 1
    funext y
    simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (hwp y).le]
    congr 1
    dsimp [r]
    field_simp [ne_of_gt (hwp y)]
  refine ⟨r, hr, hn, ?_, ?_, ?_⟩
  · intro s x
    have hlin : (∫⁻ y, ENNReal.ofReal (r s x y) ∂physicalReversibleMeasure ω hd lam) =
        ENNReal.ofReal (s : ℝ)⁻¹ := by
      have he := congrArg (fun μ : Measure (Vec d) => μ Set.univ) (hmeasure s x)
      simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at he
      rw [he, ← ofReal_integral_eq_lintegral_ofReal (hqm s x).1 (ae_of_all _ (hqn s x)), (hqm s x).2]
    have hrx : Measurable (r s x) := hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hi : Integrable (r s x) (physicalReversibleMeasure ω hd lam) := by
      have h := integrable_toReal_of_lintegral_ne_top hrx.ennreal_ofReal.aemeasurable (by rw [hlin]; exact ENNReal.ofReal_ne_top)
      simpa only [ENNReal.toReal_ofReal (hn s x _)] using h
    refine ⟨hi, ?_⟩
    have he := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (hn s x))
    rw [hlin] at he
    have he' := congrArg ENNReal.toReal he
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (hn s x)),
      ENNReal.toReal_ofReal (inv_nonneg.mpr s.property.le)] using he'
  · intro s x g
    rw [hqr s x g]
    have hrx : Measurable (r s x) := hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hqx : Measurable (q s x) := hq.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have he := congrArg (fun μ : Measure (Vec d) => ∫ y, g y ∂μ) (hmeasure s x)
    rw [integral_withDensity_eq_integral_toReal_smul hrx.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top),
      integral_withDensity_eq_integral_toReal_smul hqx.ennreal_ofReal
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at he
    simpa only [ENNReal.toReal_ofReal (hn s x _), ENNReal.toReal_ofReal (hqn s x _), smul_eq_mul] using he.symm

  · intro s t x
    have hac : physicalReversibleMeasure ω hd lam ≪ (volume : Measure (Vec d)) :=
      withDensity_absolutelyContinuous _ _
    have hid := hac.ae_le (hident s t x)
    have hi (a : MarkovProcess.Semigroup.PositiveShift) :
        Integrable (r a x) (physicalReversibleMeasure ω hd lam) := by
      have hlin : (∫⁻ y, ENNReal.ofReal (r a x y) ∂physicalReversibleMeasure ω hd lam) =
          ENNReal.ofReal (a : ℝ)⁻¹ := by
        have he := congrArg (fun μ : Measure (Vec d) => μ Set.univ) (hmeasure a x)
        simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at he
        rw [he, ← ofReal_integral_eq_lintegral_ofReal (hqm a x).1 (ae_of_all _ (hqn a x)), (hqm a x).2]
      have hrx : Measurable (r a x) := hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
      have h := integrable_toReal_of_lintegral_ne_top hrx.ennreal_ofReal.aemeasurable (by rw [hlin]; exact ENNReal.ofReal_ne_top)
      simpa only [ENNReal.toReal_ofReal (hn a x _)] using h
    have mass (a : MarkovProcess.Semigroup.PositiveShift) :
        (∫ y, r a x y ∂physicalReversibleMeasure ω hd lam) = (a : ℝ)⁻¹ := by
      have he := ofReal_integral_eq_lintegral_ofReal (hi a) (ae_of_all _ (hn a x))
      have hh := congrArg (fun μ : Measure (Vec d) => μ Set.univ) (hmeasure a x)
      simp only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] at hh
      rw [hh, ← ofReal_integral_eq_lintegral_ofReal (hqm a x).1 (ae_of_all _ (hqn a x)), (hqm a x).2] at he
      have he' := congrArg ENNReal.toReal he
      simpa only [ENNReal.toReal_ofReal (integral_nonneg (hn a x)),
        ENNReal.toReal_ofReal (inv_nonneg.mpr a.property.le)] using he'
    have hsub : (∫ y, (r s x y - r t x y) ∂physicalReversibleMeasure ω hd lam) =
        (s : ℝ)⁻¹ - (t : ℝ)⁻¹ := by
      rw [integral_sub (hi s) (hi t), mass s, mass t]
    by_cases hst : (s : ℝ) ≤ (t : ℝ)
    · have hsign : ∀ᵐ y ∂physicalReversibleMeasure ω hd lam, 0 ≤ r s x y - r t x y := by
        filter_upwards [hid] with y hy
        have hq : 0 ≤ ∫ z, q s x z * q t z y := integral_nonneg fun z => mul_nonneg (hqn _ _ _) (hqn _ _ _)
        have hh : 0 ≤ q s x y - q t x y := by rw [hy]; exact mul_nonneg (sub_nonneg.mpr hst) hq
        dsimp [r]; exact sub_nonneg.mpr ((div_le_div_iff_of_pos_right (hwp y)).mpr (sub_nonneg.mp hh))
      rw [← hsub, abs_of_nonneg (integral_nonneg_of_ae hsign)]
      exact integral_congr_ae (hsign.mono fun y hy => abs_of_nonneg hy)
    · have hsign : ∀ᵐ y ∂physicalReversibleMeasure ω hd lam, r s x y - r t x y ≤ 0 := by
        filter_upwards [hid] with y hy
        have hq : 0 ≤ ∫ z, q s x z * q t z y := integral_nonneg fun z => mul_nonneg (hqn _ _ _) (hqn _ _ _)
        have hh : q s x y - q t x y ≤ 0 := by rw [hy]; exact mul_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr (le_of_not_ge hst)) hq
        dsimp [r]; exact sub_nonpos.mpr ((div_le_div_iff_of_pos_right (hwp y)).mpr (sub_nonpos.mp hh))
      rw [← hsub, abs_of_nonpos (integral_nonpos_of_ae hsign), ← integral_neg]
      exact integral_congr_ae (hsign.mono fun y hy => abs_of_nonpos hy)

#print axioms u6_regular_signed_green_shift_L1_variation

end EinsteinFull
