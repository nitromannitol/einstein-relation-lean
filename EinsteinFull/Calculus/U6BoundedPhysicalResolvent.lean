import EinsteinFull.Calculus.U6RegularPathResolvent
import EinsteinFull.Calculus.U5RegularStoppingRestart
import EinsteinFull.Calculus.U6RegularPathRealization
import EinsteinFull.Calculus.U7RegularKernelDensity
import EinsteinFull.Calculus.U2GMPEnvironmentRealization
import EinsteinFull.Blueprint.G1.Proofs.SbxS9RealizationUniqueness
import EinsteinRelation.Diffusion.PathLawUniquenessSupport
import EinsteinRelation.Diffusion.StoppedPathLocality
import Mathlib.Data.List.Sort
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

open EinsteinRelation EinsteinRelation.SpatialDirichlet MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

namespace EinsteinFull

/-- The discounted physical kernel action on a bounded observation. -/
noncomputable def u6RegularBoundedPhysicalResolvent
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (s : ℝ) (g : Vec d → ℝ) (x : Vec d) : ℝ :=
  ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) *
    (∫ y, g y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t.toNNReal x)

/-- On continuous functions vanishing at infinity, the physical Laplace integral is
    the existing C₀ resolvent. -/
theorem u6_regular_bounded_physical_resolvent_eq_c0
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (s : ℝ) (hs : 0 < s)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ) (x : Vec d) :
    u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g x =
      u2RegularC0Resolvent hd ω lam Λ hΛ hω s hs g x := by
  let S := u2RegularC0Semigroup hd ω lam Λ hΛ hω
  let ev : ZeroAtInftyContinuousMap (Vec d) ℝ →L[ℝ] ℝ :=
    LinearMap.mkContinuous
      { toFun := fun f => f x
        map_add' := by intro f h; rfl
        map_smul' := by intro c f; rfl } 1 (by
          intro f
          simpa using BoundedContinuousFunction.norm_coe_le_norm f.toBCF x)
  have heval : (fun t : ℝ => Real.exp (-s * t) *
      (∫ y, g y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t.toNNReal x)) =
      fun t => ev (S.laplaceIntegrand s g t) := by
    funext t
    rw [u2RegularC0KernelSemigroup_integral]
    simp [MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply, ev, S]
  calc
    _ = ev (∫ t in Set.Ioi 0, S.laplaceIntegrand s g t) := by
      unfold u6RegularBoundedPhysicalResolvent
      rw [heval]
      simpa only [Function.comp_def] using (ev.integral_comp_comm (S.integrableOn_laplaceIntegrand hs g))
    _ = ev (S.resolvent ⟨s, hs⟩ g) := by rw [S.resolvent_apply]
    _ = _ := by rw [show S.resolvent ⟨s, hs⟩ = _ from
      u2_regular_c0_semigroup_resolvent hd ω lam Λ hΛ hω ⟨s, hs⟩]; rfl

/-- A jointly measurable heat density represents the physical Laplace integral
    for every bounded measurable observation. -/
theorem u6_bounded_physical_resolvent_density
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
    (g : Vec d → ℝ) (hg : Measurable g) (B : ℝ) (hbound : ∀ y, |g y| ≤ B)
    (x : Vec d) :
    u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g x = ∫ y, r x y * g y := by
  let μ : Measure ℝ := volume.restrict (Set.Ioi 0)
  let F : ℝ × Vec d → ℝ := fun z => Real.exp (-s * z.1) * p z.1.toNNReal x z.2
  have hF : Measurable F := ((Real.continuous_exp.measurable.comp
      (measurable_const.mul measurable_fst)).mul
    (hp.comp ((continuous_real_toNNReal.measurable.comp measurable_fst).prodMk
      (measurable_const.prodMk measurable_snd))))
  have hFn (z : ℝ × Vec d) : 0 ≤ F z := mul_nonneg (Real.exp_nonneg _) (hn _ _ _)
  have hnorm : ∀ᵐ t ∂μ, (∫ y, ‖F (t, y)‖) = Real.exp (-s * t) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    simp only [Real.norm_eq_abs, F, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (hn _ _ _)),
      integral_const_mul, (hrep t.toNNReal (Real.toNNReal_pos.mpr ht) x).2.1, mul_one]
  have hi : Integrable F (μ.prod volume) := by
    apply (integrable_prod_iff hF.aestronglyMeasurable).mpr
    constructor
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
      simpa only [F] using ((hrep t.toNNReal (Real.toNNReal_pos.mpr ht) x).1).const_mul (Real.exp (-s * t))
    · exact (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).congr (hnorm.mono fun _ h => h.symm)
  let H : ℝ × Vec d → ℝ := fun z => F z * g z.2
  have hH : Integrable H (μ.prod volume) := by
    apply (hi.mul_const B).mono' ((hF.mul (hg.comp measurable_snd)).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      change ‖F z * g z.2‖ ≤ F z * B
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (hFn z), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbound _) (hFn z)
  have hkernel : ∀ᵐ t ∂μ, (∫ y, H (t, y)) =
      Real.exp (-s * t) * (∫ y, g y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t.toNNReal x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    have hpmeas : Measurable (p t.toNNReal x) :=
      hp.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    rw [(hrep t.toNNReal (Real.toNNReal_pos.mpr ht) x).2.2,
      integral_withDensity_eq_integral_toReal_smul hpmeas.ennreal_ofReal
        (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top) g]
    simp only [ENNReal.toReal_ofReal (hn _ _ _), smul_eq_mul, H, F, mul_assoc, integral_const_mul]
  calc
    _ = ∫ t : ℝ in Set.Ioi 0, ∫ y, H (t, y) := by
      unfold u6RegularBoundedPhysicalResolvent
      exact integral_congr_ae (hkernel.mono fun _ h => h.symm)
    _ = ∫ y, ∫ t : ℝ in Set.Ioi 0, H (t, y) := integral_integral_swap hH
    _ = ∫ y, r x y * g y := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [H, integral_mul_const, F, ← hre x y]

/-- A single joint Green density represents every bounded measurable observation
    and satisfies the resolvent convolution identity. -/
theorem u6_regular_signed_bounded_green_representation
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ r : MarkovProcess.Semigroup.PositiveShift → Vec d → Vec d → ℝ,
      Measurable (fun z : MarkovProcess.Semigroup.PositiveShift × Vec d × Vec d =>
        r z.1 z.2.1 z.2.2) ∧
      (∀ s x y, 0 ≤ r s x y) ∧
      (∀ s x, Integrable (r s x) volume ∧ ∫ y, r s x y = (s : ℝ)⁻¹) ∧
      (∀ (s : MarkovProcess.Semigroup.PositiveShift) x (g : Vec d → ℝ),
        Measurable g → ∀ B : ℝ, (∀ y, |g y| ≤ B) →
        u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω (s : ℝ) g x =
          ∫ y, r s x y * g y) ∧
      ∀ (s t : MarkovProcess.Semigroup.PositiveShift) x, ∀ᵐ y ∂(volume : Measure (Vec d)),
        r s x y - r t x y = ((t : ℝ) - (s : ℝ)) * ∫ z, r s x z * r t z y := by
  obtain ⟨p, hp, hpn, hptime, q, hq, hqn, hqtime, hqm, hqr⟩ :=
    u6_regular_signed_joint_resolvent_time_density hd ω lam Λ hΛ hω
  obtain ⟨r, hr, hrn, hrm, hrr, hrid⟩ :=
    u6_regular_signed_resolvent_density_identity hd ω lam Λ hΛ hω
  refine ⟨r, hr, hrn, hrm, ?_, hrid⟩
  intro s x g hg B hbound
  have heq : q s x =ᵐ[volume] r s x := by
    apply u6_nonnegative_density_eq_of_c0_tests (q s x) (r s x)
      (hqm s x).1 (hrm s x).1 (hqn s x) (hrn s x)
    intro f
    rw [← hqr s x f, ← hrr s x f]
  rw [u6_bounded_physical_resolvent_density hd ω lam Λ hΛ hω (s : ℝ)
    s.property p hp hpn hptime (q s) (hqtime s) g hg B hbound x]
  apply integral_congr_ae
  filter_upwards [heq] with y hy
  rw [hy]

/-- The physical Laplace resolvent obeys the signed resolvent identity on
    bounded measurable observations at every starting point. -/
theorem u6_regular_signed_bounded_resolvent_identity
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ y, |g y| ≤ B) (x : Vec d) :
    u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g x -
      u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω t g x =
      (t - s) * u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s
        (u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω t g) x := by
  obtain ⟨r, hr, hn, hm, hrep, hid⟩ :=
    u6_regular_signed_bounded_green_representation hd ω lam Λ hΛ hω
  let a : MarkovProcess.Semigroup.PositiveShift := ⟨s, hs⟩
  let b : MarkovProcess.Semigroup.PositiveShift := ⟨t, ht⟩
  have hcont := u6_regular_signed_discounted_bounded_observable_continuous
    hd ω lam Λ hΛ hω t ht g hg B hB hbound
  have hobs : Measurable (u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω t g) :=
    hcont.1.measurable
  have hobsbound : ∀ y, |u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω t g y| ≤ B / t :=
    hcont.2
  have hb : ∀ᵐ y ∂(volume : Measure (Vec d)), ‖g y‖ ≤ B :=
    ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hbound y
  have hi1 : Integrable (fun y => r a x y * g y) volume :=
    (hm a x).1.mul_bdd hg.aestronglyMeasurable hb
  have hi2 : Integrable (fun y => r b x y * g y) volume :=
    (hm b x).1.mul_bdd hg.aestronglyMeasurable hb
  let F : Vec d × Vec d → ℝ := fun z => r a x z.1 * r b z.1 z.2
  have hiF : Integrable F (volume.prod volume) :=
    u6_resolvent_density_composition_integrable r hr hn hm a b x
  have hFm : Measurable F :=
    (hr.comp (measurable_const.prodMk (measurable_const.prodMk measurable_fst))).mul
      (hr.comp (measurable_const.prodMk (measurable_fst.prodMk measurable_snd)))
  let H : Vec d × Vec d → ℝ := fun z => F z * g z.2
  have hiH : Integrable H (volume.prod volume) := by
    apply (hiF.mul_const B).mono' ((hFm.mul (hg.comp measurable_snd)).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      change ‖F z * g z.2‖ ≤ F z * B
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hn _ _ _) (hn _ _ _)), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbound _) (mul_nonneg (hn _ _ _) (hn _ _ _))
  rw [hrep a x g hg B hbound, hrep b x g hg B hbound,
    hrep a x _ hobs (B / t) hobsbound]
  have hinner (z : Vec d) :
      u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω t g z =
        ∫ y, r b z y * g y := hrep b z g hg B hbound
  simp_rw [hinner]
  rw [← integral_sub hi1 hi2]
  have he : (∫ y, (r a x y * g y - r b x y * g y)) =
      (t - s) * ∫ y, (∫ z, F (z, y)) * g y := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [hid a b x] with y hy
    change r a x y - r b x y = (t - s) * ∫ z, F (z, y) at hy
    rw [← sub_mul, hy, mul_assoc]
  rw [he]
  congr 1
  calc
    _ = ∫ y, ∫ z, H (z, y) := by
      apply integral_congr_ae
      filter_upwards with y
      simp only [H, integral_mul_const]
    _ = ∫ z, ∫ y, H (z, y) := (integral_integral_swap hiH).symm
    _ = ∫ z, r a x z * ∫ y, r b z y * g y := by
      apply integral_congr_ae
      filter_upwards with z
      simp only [H, F, mul_assoc, integral_const_mul]




/-- Restart a bounded measurable compensator on each past event of the supplied realization. -/
theorem u6_regular_bounded_compensator_restart
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (f q : Vec d → ℝ) (hf : Continuous f) (hq : Measurable q)
    (C D : ℝ) (hfbound : ∀ y, |f y| ≤ C) (hqbound : ∀ y, |q y| ≤ D)
    (x : Vec d) (a b : ℝ≥0) (hab : a ≤ b) (A : Set (Path d))
    (hA : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) a] A) :
    (∫ γ in A, (f (γ b) - f (γ a) -
      ∫ u : ℝ in Set.Ioc (a : ℝ) (b : ℝ), q (γ u.toNNReal)) ∂K x) =
    ∫ γ in A, ∫ η, compensatedTest (fun _ => q) f (b - a) η ∂K (γ a) ∂K x := by
  let L : (Vec d → ℝ) → Vec d → ℝ := fun _ => q
  have hLi (γ : Path d) (c e : ℝ) :
      IntervalIntegrable (fun u => L f (γ u.toNNReal)) volume c e :=
    intervalIntegrable_path_of_bounded hq hqbound γ c e
  have ha := stronglyAdapted_compensatedTest_of_measurable L f hf hq
  have hF : Measurable (compensatedTest L f (b - a)) :=
    ((ha (b - a)).mono ((pathFiltration d).le (b - a))).measurable
  have hbound (γ : Path d) :
      ‖compensatedTest L f (b - a) γ‖ ≤ 2 * C + D * ((b - a : ℝ≥0) : ℝ) :=
    abs_compensatedTest_le (L := L) (φ := f)
      (fun y => by simpa only [Real.norm_eq_abs] using hfbound y)
      (fun y => by simpa only [L, Real.norm_eq_abs] using hqbound y) (b - a) γ
  have hA' : MeasurableSet[pathFiltration d a] A := by
    rw [pathFiltration_eq_canonical]
    exact hA
  have he := u5_regular_integral_shift_on_past hd ω lam Λ hΛ hω K hfdd x a A hA'
    (compensatedTest L f (b - a)) hF _ hbound
  simp_rw [u5_compensatedTest_shift L f hLi a (b - a), add_tsub_cancel_of_le hab] at he
  have heq (γ : Path d) : compensatedTest L f b γ - compensatedTest L f a γ =
      f (γ b) - f (γ a) - ∫ u : ℝ in Set.Ioc (a : ℝ) (b : ℝ), q (γ u.toNNReal) := by
    rw [← intervalIntegral.integral_of_le (show (a : ℝ) ≤ b from NNReal.coe_le_coe.mpr hab)]
    have hadd := intervalIntegral.integral_add_adjacent_intervals (hLi γ 0 a) (hLi γ a b)
    simp only [compensatedTest, L] at hadd ⊢
    linarith
  simpa only [heq] using he


/-- Restart the literal bounded-observation resolvent compensator. -/
theorem u6_regular_signed_bounded_resolvent_restart
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ y, |g y| ≤ B)
    (a b : ℝ≥0) (hab : a ≤ b) (A : Set (Path d))
    (hA : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) a] A) :
    let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
    (∫ γ in A, (R (γ b) - R (γ a) -
      ∫ u : ℝ in Set.Ioc (a : ℝ) (b : ℝ),
        (s * R (γ u.toNNReal) - g (γ u.toNNReal))) ∂K x) =
    ∫ γ in A, ∫ η, compensatedTest (fun _ y => s * R y - g y) R (b - a) η
      ∂K (γ a) ∂K x := by
  dsimp only
  let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
  have hR := u6_regular_signed_discounted_bounded_observable_continuous
    hd ω lam Λ hΛ hω s hs g hg B hB hbound
  have hq : Measurable (fun y => s * R y - g y) :=
    (measurable_const.mul hR.1.measurable).sub hg
  have hqbound (y : Vec d) : |s * R y - g y| ≤ 2 * B := by
    calc
      |s * R y - g y| ≤ |s * R y| + |g y| := abs_sub _ _
      _ = s * |R y| + |g y| := by rw [abs_mul, abs_of_pos hs]
      _ ≤ s * (B / s) + B := add_le_add (mul_le_mul_of_nonneg_left (hR.2 y) hs.le) (hbound y)
      _ = 2 * B := by field_simp [ne_of_gt hs]; ring
  exact u6_regular_bounded_compensator_restart hd ω lam Λ hΛ hω K hfdd
    R (fun y => s * R y - g y) hR.1 hq (B / s) (2 * B) hR.2 hqbound x a b hab A hA


/-- Discounted occupation under the supplied path law equals the literal
    bounded-observation physical resolvent. -/
theorem u6_regular_signed_bounded_path_laplace
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hbound : ∀ y, |g y| ≤ B) :
    (∫ γ : Path d, (∫ t : ℝ in Set.Ioi 0,
      Real.exp (-s * t) * g (γ t.toNNReal)) ∂K x) =
      u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g x := by
  have heval : Continuous (fun z : ℝ × Path d => z.2 z.1.toNNReal) :=
    continuous_eval.comp
      (continuous_snd.prodMk (continuous_real_toNNReal.comp continuous_fst))
  have hi : Integrable (fun z : ℝ × Path d => Real.exp (-s * z.1) *
      g (z.2 z.1.toNNReal)) ((volume.restrict (Set.Ioi 0)).prod (K x)) := by
    apply (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const B).comp_fst
      (K x)).mono'
      (((Real.continuous_exp.measurable.comp (measurable_const.mul measurable_fst)).mul
        (hg.comp heval.measurable)).aestronglyMeasurable)
    exact ae_of_all _ fun z => by
      change ‖Real.exp (-s * z.1) * g (z.2 z.1.toNNReal)‖ ≤ Real.exp (-s * z.1) * B
      rw [norm_mul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hbound _) (Real.exp_nonneg _)
  unfold u6RegularBoundedPhysicalResolvent
  rw [← integral_integral_swap hi]
  apply integral_congr_ae
  filter_upwards with t
  rw [integral_const_mul]
  congr 1
  rw [← Blueprint.k11_endpoint _ K hfdd t.toNNReal x]
  exact (integral_map (measurable_pathPosition t.toNNReal).aemeasurable
    hg.aestronglyMeasurable).symm


/-- A bounded measurable path occupation splits at a deterministic time. -/
theorem u6_bounded_discounted_path_integral_split {d : ℕ} (γ : Path d)
    (g : Vec d → ℝ) (hg : Measurable g) (B : ℝ)
    (hbound : ∀ y, |g y| ≤ B) (s : ℝ) (hs : 0 < s) (a : ℝ≥0) :
    (∫ u : ℝ in Set.Ioc (0 : ℝ) (a : ℝ), Real.exp (-s * u) * g (γ u.toNNReal)) +
      Real.exp (-s * (a : ℝ)) *
        (∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g (γ (a + u.toNNReal))) =
    ∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g (γ u.toNNReal) := by
  let f : ℝ → ℝ := fun u => Real.exp (-s * u) * g (γ u.toNNReal)
  have hE : IntegrableOn (fun u : ℝ => B * Real.exp (-s * u)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul B
  have hf : IntegrableOn f (Set.Ioi 0) := by
    apply hE.mono' (((Real.continuous_exp.measurable.comp (measurable_const.mul measurable_id)).mul
      (hg.comp (γ.continuous.comp continuous_real_toNNReal).measurable)).aestronglyMeasurable)
    exact ae_of_all _ fun u => by
      change ‖Real.exp (-s * u) * g (γ u.toNNReal)‖ ≤ B * Real.exp (-s * u)
      rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (hbound _) (Real.exp_nonneg _)
  have htail : (∫ u : ℝ in Set.Ioi 0, f ((a : ℝ) + u)) =
      Real.exp (-s * (a : ℝ)) *
        (∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g (γ (a + u.toNNReal))) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    simp only [Set.mem_Ioi] at hu
    dsimp only [f]
    rw [show -s * ((a : ℝ) + u) = -s * (a : ℝ) + -s * u by ring, Real.exp_add,
      Real.toNNReal_add (NNReal.coe_nonneg a) hu.le]
    simp only [Real.toNNReal_coe]
    ring
  have he := u5_integral_Ioi_split_translate f (a : ℝ) (NNReal.coe_nonneg a) hf
  rw [htail] at he
  exact he


/-- The discounted future occupation restarts from the current position under
    the supplied finite-dimensional laws. -/
theorem u6_regular_signed_bounded_shifted_path_laplace
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hbound : ∀ y, |g y| ≤ B) (a : ℝ≥0) :
    (∫ γ : Path d, (∫ t : ℝ in Set.Ioi 0,
      Real.exp (-s * t) * g (γ (a + t.toNNReal))) ∂K x) =
      ∫ γ : Path d, u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g (γ a) ∂K x := by
  let Φ : Path d → ℝ := fun γ => ∫ t : ℝ in Set.Ioi 0,
    Real.exp (-s * t) * g (γ t.toNNReal)
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk
      (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hm : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * g (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul (hg.comp heval)
  have hΦ : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hm.stronglyMeasurable).measurable
  let E : ℝ → ℝ := fun t => Real.exp (-s * t) * |B|
  have hE : IntegrableOn E (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const |B|
  have hb (γ : Path d) : ‖Φ γ‖ ≤ ∫ t in Set.Ioi (0 : ℝ), E t := by
    refine norm_integral_le_of_norm_le hE (ae_of_all _ fun t => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs]
    dsimp only [E]
    exact mul_le_mul_of_nonneg_left ((hbound _).trans (le_abs_self B)) (Real.exp_nonneg _)
  have hA : MeasurableSet[pathFiltration d a] (Set.univ : Set (Path d)) := MeasurableSet.univ
  have he := u5_regular_integral_shift_on_past hd ω lam Λ hΛ hω K hfdd x a Set.univ hA
    Φ hΦ _ hb
  simp only [Measure.restrict_univ] at he
  have hmean (y : Vec d) : (∫ η, Φ η ∂K y) =
      u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g y :=
    u6_regular_signed_bounded_path_laplace hd ω lam Λ hΛ hω K hfdd y s hs g hg B hbound
  simp_rw [hmean] at he
  simpa only [Φ, gmpShiftPath, ContinuousMap.coe_mk] using he



/-- The literal bounded resolvent satisfies the discounted occupation identity
    under every supplied path realization. -/
theorem u6_regular_signed_bounded_discounted_occupation
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ y, |g y| ≤ B) (a : ℝ≥0) :
    let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
    (∫ γ : Path d, (Real.exp (-s * (a : ℝ)) * R (γ a) +
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (a : ℝ),
        Real.exp (-s * t) * g (γ t.toNNReal)) ∂K x) = R x := by
  dsimp only
  let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
  let Φ : Path d → ℝ := fun γ => ∫ t : ℝ in Set.Ioi 0,
    Real.exp (-s * t) * g (γ t.toNNReal)
  let f : Path d → ℝ := fun γ => Φ (gmpShiftPath a γ)
  let r : Path d → ℝ := fun γ => R (γ a)
  let c : ℝ := Real.exp (-s * (a : ℝ))
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk
      (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hm : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * g (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul (hg.comp heval)
  have hΦm : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hm.stronglyMeasurable).measurable
  let E : ℝ → ℝ := fun t => Real.exp (-s * t) * B
  have hE : IntegrableOn E (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const B
  have hb (γ : Path d) : ‖Φ γ‖ ≤ ∫ t in Set.Ioi (0 : ℝ), E t := by
    refine norm_integral_le_of_norm_le hE (ae_of_all _ fun t => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left (hbound _) (Real.exp_nonneg _)
  have hΦ : Integrable Φ (K x) := Integrable.of_bound hΦm.aestronglyMeasurable _ (ae_of_all _ hb)
  have hf : Integrable f (K x) := Integrable.of_bound
    (hΦm.comp (measurable_gmpShiftPath a)).aestronglyMeasurable _ (ae_of_all _ fun γ => hb _)
  have hR := u6_regular_signed_discounted_bounded_observable_continuous
    hd ω lam Λ hΛ hω s hs g hg B hB hbound
  have hr : Integrable r (K x) := Integrable.of_bound
    (hR.1.measurable.comp (measurable_pathPosition a)).aestronglyMeasurable _
    (ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs, r, R, u6RegularBoundedPhysicalResolvent] using hR.2 (γ a))
  have he : (∫ γ, f γ ∂K x) = ∫ γ, r γ ∂K x := by
    simpa only [f, r, Φ, gmpShiftPath, ContinuousMap.coe_mk] using
      u6_regular_signed_bounded_shifted_path_laplace hd ω lam Λ hΛ hω K hfdd x s hs g hg B hbound a
  have hpath : (∫ γ, Φ γ ∂K x) = R x :=
    u6_regular_signed_bounded_path_laplace hd ω lam Λ hΛ hω K hfdd x s hs g hg B hbound
  change (∫ γ, c * r γ + (∫ t : ℝ in Set.Ioc (0 : ℝ) (a : ℝ),
    Real.exp (-s * t) * g (γ t.toNNReal)) ∂K x) = R x
  calc
    _ = ∫ γ, (Φ γ + c * r γ) - c * f γ ∂K x := by
      apply integral_congr_ae
      filter_upwards with γ
      have hp := u6_bounded_discounted_path_integral_split γ g hg B hbound s hs a
      change (∫ t : ℝ in Set.Ioc (0 : ℝ) (a : ℝ),
        Real.exp (-s * t) * g (γ t.toNNReal)) + c * f γ = Φ γ at hp
      linarith
    _ = (∫ γ, Φ γ ∂K x) + (∫ γ, c * r γ ∂K x) -
        (∫ γ, c * f γ ∂K x) := by
      have hi := integral_sub (hΦ.add (hr.const_mul c)) (hf.const_mul c)
      simp only [Pi.add_apply] at hi
      rw [integral_add hΦ (hr.const_mul c)] at hi
      exact hi
    _ = R x := by rw [integral_const_mul, integral_const_mul, he, hpath]; ring



/-- Fubini for bounded weighted occupation along continuous paths. -/
theorem u6_bounded_weighted_path_occupation {d : ℕ}
    (μ : Measure (Path d)) [IsFiniteMeasure μ]
    (w : ℝ → ℝ) (hw : Measurable w) (C : ℝ) (hC : 0 ≤ C)
    (hwbound : ∀ t, |w t| ≤ C)
    (q : Vec d → ℝ) (hq : Measurable q) (D : ℝ)
    (hqbound : ∀ y, |q y| ≤ D) (T : ℝ≥0) :
    Integrable (fun γ : Path d => ∫ u : ℝ in Set.Ioc (0 : ℝ) (T : ℝ),
      w u * q (γ u.toNNReal)) μ ∧
    (∫ γ : Path d, (∫ u : ℝ in Set.Ioc (0 : ℝ) (T : ℝ),
      w u * q (γ u.toNNReal)) ∂μ) =
      ∫ u : ℝ in Set.Ioc (0 : ℝ) (T : ℝ), w u * (∫ γ : Path d, q (γ u.toNNReal) ∂μ) := by
  let ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) T)
  let H : Path d × ℝ → ℝ := fun z => w z.2 * q (z.1 z.2.toNNReal)
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    continuous_eval.measurable.comp
      (measurable_fst.prodMk (measurable_real_toNNReal.comp measurable_snd))
  have hH : Measurable H := (hw.comp measurable_snd).mul (hq.comp heval)
  have hint : Integrable H (μ.prod ν) := by
    apply Integrable.of_bound hH.aestronglyMeasurable (C * D)
    exact ae_of_all _ fun z => by
      change ‖w z.2 * q (z.1 z.2.toNNReal)‖ ≤ C * D
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      exact mul_le_mul (hwbound _) (hqbound _) (abs_nonneg _) hC
  constructor
  · exact hint.integral_prod_left
  · calc
      _ = ∫ u, ∫ γ, H (γ, u) ∂μ ∂ν := integral_integral_swap hint
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with u
        exact integral_const_mul (w u) (fun γ : Path d => q (γ u.toNNReal))



/-- Product rule for a time weight and an indefinite Lebesgue integral. -/
theorem u6_integral_product_indefinite {a b : ℝ} (hab : a ≤ b)
    {W G L : ℝ → ℝ} (hW : AbsolutelyContinuousOnInterval W a b)
    (hL : IntervalIntegrable L volume a b)
    (hWG : ∀ᵐ u ∂(volume.restrict (Set.Ioc a b)), deriv W u = G u) :
    W b * (∫ u in a..b, L u) =
      ∫ u in a..b, G u * (∫ v in a..u, L v) + W u * L u := by
  let A : ℝ → ℝ := fun u => ∫ v in a..u, L v
  have hA : AbsolutelyContinuousOnInterval A a b :=
    hL.absolutelyContinuousOnInterval_intervalIntegral (by simp)
  have hda : ∀ᵐ u ∂(volume.restrict (Set.Ioc a b)), deriv A u = L u := by
    filter_upwards [ae_restrict_of_ae hL.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_Ioc] with u hu hmem
    have humem : u ∈ Set.uIcc a b := by
      rw [Set.uIcc_of_le hab]; exact ⟨hmem.1.le, hmem.2⟩
    exact (hu humem a (by simp)).deriv
  have hp := hW.integral_deriv_mul_eq_sub hA
  have heq : (∫ u in a..b, deriv W u * A u + W u * deriv A u) =
      ∫ u in a..b, G u * A u + W u * L u := by
    rw [intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hab]
    apply integral_congr_ae
    filter_upwards [hWG, hda] with u huW huA
    rw [huW, huA]
  rw [heq] at hp
  simpa [A] using hp.symm



/-- The discounted identity expressed in terms of the two time marginals. -/
theorem u6_regular_signed_bounded_discounted_mean
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ y, |g y| ≤ B) (a : ℝ≥0) :
    let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
    Real.exp (-s * (a : ℝ)) * (∫ γ : Path d, R (γ a) ∂K x) +
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (a : ℝ), Real.exp (-s * t) *
        (∫ γ : Path d, g (γ t.toNNReal) ∂K x)) = R x := by
  dsimp only
  let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
  let w : ℝ → ℝ := fun t => Real.exp (-s * max t 0)
  have hw : Measurable w := by fun_prop
  have hwb (t : ℝ) : |w t| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (le_max_right t 0))
  have hocc := u6_bounded_weighted_path_occupation (K x) w hw 1 zero_le_one hwb
    g hg B hbound a
  have heq (γ : Path d) :
      (∫ t : ℝ in Set.Ioc (0 : ℝ) (a : ℝ), w t * g (γ t.toNNReal)) =
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (a : ℝ), Real.exp (-s * t) * g (γ t.toNNReal) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
    simp only [w, max_eq_left ht.1.le]
  have hoccI : Integrable (fun γ : Path d =>
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (a : ℝ), Real.exp (-s * t) * g (γ t.toNNReal)) (K x) := by
    simpa only [heq] using hocc.1
  have hoccE : (∫ γ : Path d, (∫ t : ℝ in Set.Ioc (0 : ℝ) (a : ℝ),
      Real.exp (-s * t) * g (γ t.toNNReal)) ∂K x) =
      ∫ t : ℝ in Set.Ioc (0 : ℝ) (a : ℝ), Real.exp (-s * t) *
        (∫ γ : Path d, g (γ t.toNNReal) ∂K x) := by
    calc
      _ = ∫ γ : Path d, (∫ t : ℝ in Set.Ioc (0 : ℝ) (a : ℝ), w t * g (γ t.toNNReal)) ∂K x := by
        apply integral_congr_ae
        filter_upwards with γ
        exact (heq γ).symm
      _ = ∫ t : ℝ in Set.Ioc (0 : ℝ) (a : ℝ), w t *
          (∫ γ : Path d, g (γ t.toNNReal) ∂K x) := hocc.2
      _ = _ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
        simp only [w, max_eq_left ht.1.le]
  have hR := u6_regular_signed_discounted_bounded_observable_continuous
    hd ω lam Λ hΛ hω s hs g hg B hB hbound
  have hr : Integrable (fun γ : Path d => Real.exp (-s * (a : ℝ)) * R (γ a)) (K x) := by
    apply Integrable.const_mul _ _
    apply Integrable.of_bound (hR.1.measurable.comp (measurable_pathPosition a)).aestronglyMeasurable (B / s)
    exact ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs, R, u6RegularBoundedPhysicalResolvent, Function.comp_apply, pathPosition] using hR.2 (γ a)
  have he := u6_regular_signed_bounded_discounted_occupation hd ω lam Λ hΛ hω K hfdd x s hs g hg B hB hbound a
  dsimp only at he
  rw [integral_add hr hoccI, integral_const_mul, hoccE] at he
  exact he



/-- Product rule for an exponential and a discounted occupation remainder. -/
theorem u6_exponential_occupation_remainder {T s c : ℝ} (hT : 0 ≤ T)
    {L : ℝ → ℝ} (hL : IntervalIntegrable L volume 0 T) :
    Real.exp (s * T) * (c - ∫ u in (0 : ℝ)..T, L u) - c =
      ∫ u in (0 : ℝ)..T, s * Real.exp (s * u) *
        (c - ∫ v in (0 : ℝ)..u, L v) - Real.exp (s * u) * L u := by
  let W : ℝ → ℝ := fun u => Real.exp (s * u)
  let A : ℝ → ℝ := fun u => c - ∫ v in (0 : ℝ)..u, L v
  have hW : AbsolutelyContinuousOnInterval W 0 T :=
    (show ContDiff ℝ 1 W by dsimp [W]; fun_prop).contDiffOn.absolutelyContinuousOnInterval
  have hAc : AbsolutelyContinuousOnInterval A 0 T := by
    have hc : AbsolutelyContinuousOnInterval (fun _ : ℝ => c) 0 T :=
      (show ContDiff ℝ 1 (fun _ : ℝ => c) by fun_prop).contDiffOn.absolutelyContinuousOnInterval
    exact hc.sub (hL.absolutelyContinuousOnInterval_intervalIntegral (by simp))
  have hda : ∀ᵐ u ∂(volume.restrict (Set.Ioc (0 : ℝ) T)), deriv A u = -L u := by
    filter_upwards [ae_restrict_of_ae hL.ae_hasDerivAt_integral,
      ae_restrict_mem measurableSet_Ioc] with u hu hmem
    have humem : u ∈ Set.uIcc (0 : ℝ) T := by
      rw [Set.uIcc_of_le hT]; exact ⟨hmem.1.le, hmem.2⟩
    have hd := (hasDerivAt_const u c).sub (hu humem 0 (by simp))
    have hfun : ((fun _ : ℝ => c) - (fun v => ∫ z in (0 : ℝ)..v, L z)) = A := by
      funext v
      rfl
    rw [hfun] at hd
    simpa only [zero_sub] using hd.deriv
  have hdW (u : ℝ) : deriv W u = s * Real.exp (s * u) := by
    simpa only [W, id_eq, mul_comm, mul_one] using
      (((hasDerivAt_id u).const_mul s).exp).deriv
  have hp := hW.integral_deriv_mul_eq_sub hAc
  have heq : (∫ u in (0 : ℝ)..T, deriv W u * A u + W u * deriv A u) =
      ∫ u in (0 : ℝ)..T, s * Real.exp (s * u) * A u - Real.exp (s * u) * L u := by
    rw [intervalIntegral.integral_of_le hT, intervalIntegral.integral_of_le hT]
    apply integral_congr_ae
    filter_upwards [hda] with u hu
    rw [hdW, hu]
    simp only [W, mul_neg, sub_eq_add_neg]
  rw [heq] at hp
  simpa [W, A] using hp.symm



/-- A discounted mean identity implies its undiscounted integral equation. -/
theorem u6_discounted_mean_to_integral {T s c : ℝ} (hT : 0 ≤ T)
    (F H : ℝ → ℝ)
    (hL : IntervalIntegrable (fun u => Real.exp (-s * u) * H u) volume 0 T)
    (hrel : ∀ u ∈ Set.Icc (0 : ℝ) T,
      Real.exp (-s * u) * F u +
        (∫ v in (0 : ℝ)..u, Real.exp (-s * v) * H v) = c) :
    F T - c = ∫ u in (0 : ℝ)..T, s * F u - H u := by
  let L : ℝ → ℝ := fun u => Real.exp (-s * u) * H u
  have hex (u : ℝ) : Real.exp (s * u) * Real.exp (-s * u) = 1 := by
    rw [← Real.exp_add]
    simp
  have hf (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) T) :
      Real.exp (s * u) * (c - ∫ v in (0 : ℝ)..u, L v) = F u := by
    have hr := hrel u hu
    change Real.exp (-s * u) * F u + (∫ v in (0 : ℝ)..u, L v) = c at hr
    rw [show c - (∫ v in (0 : ℝ)..u, L v) = Real.exp (-s * u) * F u by linarith]
    rw [← mul_assoc, hex, one_mul]
  have hp := u6_exponential_occupation_remainder (s := s) (c := c) hT hL
  calc
    F T - c = Real.exp (s * T) * (c - ∫ u in (0 : ℝ)..T, L u) - c := by
      rw [hf T ⟨hT, le_rfl⟩]
    _ = ∫ u in (0 : ℝ)..T, s * Real.exp (s * u) *
        (c - ∫ v in (0 : ℝ)..u, L v) - Real.exp (s * u) * L u := hp
    _ = ∫ u in (0 : ℝ)..T, s * F u - H u := by
      apply intervalIntegral.integral_congr
      intro u hu
      rw [Set.uIcc_of_le hT] at hu
      dsimp only
      rw [mul_assoc, hf u hu]
      dsimp only [L]
      rw [← mul_assoc, hex, one_mul]



/-- The literal bounded resolvent satisfies the undiscounted mean equation. -/
theorem u6_regular_signed_bounded_resolvent_mean
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ y, |g y| ≤ B) (t : ℝ≥0) :
    let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
    (∫ γ : Path d, R (γ t) ∂K x) - R x =
      ∫ u in (0 : ℝ)..(t : ℝ),
        (s * (∫ γ : Path d, R (γ u.toNNReal) ∂K x) -
          ∫ γ : Path d, g (γ u.toNNReal) ∂K x) := by
  dsimp only
  let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
  let F : ℝ → ℝ := fun u => ∫ γ : Path d, R (γ u.toNNReal) ∂K x
  let H : ℝ → ℝ := fun u => ∫ γ : Path d, g (γ u.toNNReal) ∂K x
  have heval : Measurable (fun z : ℝ × Path d => z.2 z.1.toNNReal) :=
    continuous_eval.measurable.comp
      (measurable_snd.prodMk (measurable_real_toNNReal.comp measurable_fst))
  have hHm : Measurable H :=
    ((hg.comp heval).stronglyMeasurable.integral_prod_right' (ν := K x)).measurable
  have hHb (u : ℝ) : |H u| ≤ B := by
    have hb := norm_integral_le_of_norm_le_const (μ := K x)
      (f := fun γ : Path d => g (γ u.toNNReal)) (C := B)
      (ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs] using hbound (γ u.toNNReal))
    simpa only [H, Real.norm_eq_abs, probReal_univ, mul_one] using hb
  have hL : IntervalIntegrable (fun u => Real.exp (-s * u) * H u) volume 0 t := by
    apply intervalIntegrable_iff.mpr
    apply IntegrableOn.of_bound (by simp)
      ((Real.measurable_exp.comp (measurable_const.mul measurable_id)).mul hHm).aestronglyMeasurable B
    filter_upwards [ae_restrict_mem measurableSet_uIoc] with u hu
    have hu0 : 0 ≤ u := by
      have hu' := Set.uIoc_subset_uIcc hu
      rw [Set.uIcc_of_le t.coe_nonneg] at hu'
      exact hu'.1
    have he : Real.exp (-s * u) ≤ 1 :=
      Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) hu0)
    change ‖Real.exp (-s * u) * H u‖ ≤ B
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs]
    calc
      _ ≤ 1 * B := mul_le_mul he (hHb u) (abs_nonneg _) zero_le_one
      _ = B := one_mul B
  have hrel (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) (t : ℝ)) :
      Real.exp (-s * u) * F u + (∫ v in (0 : ℝ)..u, Real.exp (-s * v) * H v) = R x := by
    have h := u6_regular_signed_bounded_discounted_mean
      hd ω lam Λ hΛ hω K hfdd x s hs g hg B hB hbound u.toNNReal
    dsimp only at h
    simpa only [F, H, R, Real.coe_toNNReal u hu.1,
      intervalIntegral.integral_of_le hu.1] using h
  have h := u6_discounted_mean_to_integral t.coe_nonneg F H hL hrel
  simpa only [F, H, Real.toNNReal_coe, R] using h



/-- The bounded physical resolvent compensator has zero mean under the supplied law. -/
theorem u6_regular_signed_bounded_resolvent_compensated_mean_zero
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ y, |g y| ≤ B) (t : ℝ≥0) :
    let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
    (∫ γ, compensatedTest (fun _ y => s * R y - g y) R t γ ∂K x) = 0 := by
  dsimp only
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
  let q : Vec d → ℝ := fun y => s * R y - g y
  have hR := u6_regular_signed_discounted_bounded_observable_continuous
    hd ω lam Λ hΛ hω s hs g hg B hB hbound
  have hq : Measurable q := (measurable_const.mul hR.1.measurable).sub hg
  have hqbound (y : Vec d) : |q y| ≤ 2 * B := by
    calc
      |s * R y - g y| ≤ |s * R y| + |g y| := abs_sub _ _
      _ = s * |R y| + |g y| := by rw [abs_mul, abs_of_pos hs]
      _ ≤ s * (B / s) + B := add_le_add (mul_le_mul_of_nonneg_left (hR.2 y) hs.le) (hbound y)
      _ = 2 * B := by field_simp [ne_of_gt hs]; ring
  have hiR (u : ℝ≥0) : Integrable (fun γ : Path d => R (γ u)) (K x) :=
    Integrable.of_bound (hR.1.measurable.comp (measurable_pathPosition u)).aestronglyMeasurable _
      (ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs, R, u6RegularBoundedPhysicalResolvent] using hR.2 (γ u))
  have hig (u : ℝ≥0) : Integrable (fun γ : Path d => g (γ u)) (K x) :=
    Integrable.of_bound (hg.comp (measurable_pathPosition u)).aestronglyMeasurable B
      (ae_of_all _ fun γ => by simpa only [Real.norm_eq_abs] using hbound (γ u))
  have h0 : (∫ γ : Path d, R (γ 0) ∂K x) = R x := by
    have hm := integral_map (μ := K x) (measurable_pathPosition 0).aemeasurable
      (f := R) hR.1.aestronglyMeasurable
    rw [Blueprint.k11_endpoint P K hfdd 0 x, P.kernel_zero, Kernel.id_apply, integral_dirac] at hm
    exact hm.symm
  have hocc := u6_bounded_weighted_path_occupation (K x) (fun _ => 1) measurable_const
    1 zero_le_one (fun _ => by simp) q hq (2 * B) hqbound t
  have hqi : Integrable (fun γ : Path d => ∫ u in (0 : ℝ)..(t : ℝ), q (γ u.toNNReal)) (K x) := by
    simpa only [intervalIntegral.integral_of_le t.coe_nonneg, one_mul] using hocc.1
  have hqe : (∫ γ : Path d, (∫ u in (0 : ℝ)..(t : ℝ), q (γ u.toNNReal)) ∂K x) =
      ∫ u in (0 : ℝ)..(t : ℝ), s * (∫ γ : Path d, R (γ u.toNNReal) ∂K x) -
        ∫ γ : Path d, g (γ u.toNNReal) ∂K x := by
    simp_rw [intervalIntegral.integral_of_le t.coe_nonneg]
    calc
      _ = ∫ u : ℝ in Set.Ioc (0 : ℝ) (t : ℝ), (∫ γ : Path d, q (γ u.toNNReal) ∂K x) := by
        simpa only [intervalIntegral.integral_of_le t.coe_nonneg, one_mul] using hocc.2
      _ = _ := by
        apply integral_congr_ae
        filter_upwards with u
        change (∫ γ : Path d, (s * R (γ u.toNNReal) - g (γ u.toNNReal)) ∂K x) = _
        rw [integral_sub ((hiR u.toNNReal).const_mul s) (hig u.toNNReal), integral_const_mul]
  have hmean := u6_regular_signed_bounded_resolvent_mean
    hd ω lam Λ hΛ hω K hfdd x s hs g hg B hB hbound t
  change (∫ γ : Path d, (R (γ t) - R (γ 0)) -
    (∫ u in (0 : ℝ)..(t : ℝ), q (γ u.toNNReal)) ∂K x) = 0
  have hh := integral_sub ((hiR t).sub (hiR 0)) hqi
  have hh2 := integral_sub (hiR t) (hiR 0)
  simp only [Pi.sub_apply] at hh hh2
  rw [hh, hh2, h0, hqe]
  exact sub_eq_zero.mpr hmean


/-- The bounded-observation physical resolvent is a martingale on every past event. -/
theorem u6_regular_signed_bounded_resolvent_martingale_events
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ y, |g y| ≤ B) :
    let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
    ∀ (a b : ℝ≥0), a ≤ b → ∀ A : Set (Path d),
      MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) a] A →
      (∫ γ in A, (R (γ b) - R (γ a) -
        ∫ u : ℝ in Set.Ioc (a : ℝ) (b : ℝ),
          (s * R (γ u.toNNReal) - g (γ u.toNNReal))) ∂K x) = 0 := by
  dsimp only
  intro a b hab A hA
  rw [u6_regular_signed_bounded_resolvent_restart hd ω lam Λ hΛ hω K hfdd
    x s hs g hg B hB hbound a b hab A hA]
  simp_rw [u6_regular_signed_bounded_resolvent_compensated_mean_zero
    hd ω lam Λ hΛ hω K hfdd _ s hs g hg B hB hbound (b - a), integral_zero]


/-- Bounded measurable discounted occupation restarts at any finite stopping time. -/
theorem u6_regular_signed_bounded_stopped_path_laplace
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B) (hbound : ∀ y, |g y| ≤ B)
    (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0))) :
    ∀ A : Set (Path d), MeasurableSet[hT.measurableSpace] A →
      (∫ γ in A, (∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) *
        g (γ (T γ + t.toNNReal))) ∂K x) =
      ∫ γ in A, u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
        (γ (T γ)) ∂K x := by
  intro A hA
  have hrestart := u5_regular_signed_realization_stopping_restart
    hd ω lam Λ hΛ hω K hfdd x T hT A hA
  let Φ : Path d → ℝ := fun η => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * g (η t.toNNReal)
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hgm : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * g (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul
      (hg.comp heval)
  have hΦm : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hgm.stronglyMeasurable).measurable
  have hexp : IntegrableOn (fun t : ℝ => max B 0 * Real.exp (-s * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul (max B 0)
  have hbd (η : Path d) : ‖Φ η‖ ≤ ∫ t in Set.Ioi (0 : ℝ), max B 0 * Real.exp (-s * t) := by
    refine norm_integral_le_of_norm_le hexp (ae_of_all _ fun t => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (by simpa only [max_eq_left hB] using hbound (η t.toNNReal))
      (Real.exp_nonneg _)
  have hΦi (μ : Measure (Path d)) [IsFiniteMeasure μ] : Integrable Φ μ :=
    Integrable.of_bound hΦm.aestronglyMeasurable _ (ae_of_all _ hbd)
  have hswap (y : Vec d) :
      (∫ η, Φ η ∂K y) = u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g y :=
    u6_regular_signed_bounded_path_laplace hd ω lam Λ hΛ hω K hfdd y s hs g hg B hbound
  have hshift := MarkovProcess.ContinuousPath.measurable_shift_stoppingTime T hT
  calc
    _ = ∫ η, Φ η ∂((K x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ) := by
      rw [integral_map hshift.aemeasurable hΦm.aestronglyMeasurable]
      rfl
    _ = ∫ η, Φ η ∂(Kernel.comap K (fun γ => γ (T γ))
          (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT) ∘ₘ
            ((K x).restrict A)) := by rw [hrestart]
    _ = _ := by
      rw [Measure.comp_eq_comp_const_apply, Kernel.integral_comp]
      · simp only [Kernel.const_apply, Kernel.comap_apply, hswap]
      · exact hΦi _



/-- Discounted bounded measurable occupation over growing finite intervals converges
    to occupation over the positive half-line. -/
theorem u6_bounded_discounted_path_occupation_tendsto {d : ℕ} (γ : Path d)
    (g : Vec d → ℝ) (hg : Measurable g) (B : ℝ)
    (hb : ∀ y, |g y| ≤ B) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun n : ℕ => ∫ u : ℝ in Set.Ioc (0 : ℝ) (n : ℝ),
      Real.exp (-s * u) * g (γ u.toNNReal)) atTop
      (𝓝 (∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g (γ u.toNNReal))) := by
  let v : ℕ → ℝ := fun n => ∫ u : ℝ in Set.Ioi 0,
    Real.exp (-s * u) * g (γ ((n : ℝ≥0) + u.toNNReal))
  have hE : IntegrableOn (fun u : ℝ => B * Real.exp (-s * u)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul B
  have hv : ∀ n, ‖v n‖ ≤ ∫ u in Set.Ioi (0 : ℝ), B * Real.exp (-s * u) := by
    intro n
    refine norm_integral_le_of_norm_le hE (ae_of_all _ fun u => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hb _) (Real.exp_nonneg _)
  have hz := u5_exp_discount_bounded_tendsto_zero s hs v _ hv
  have hc : Tendsto (fun _ : ℕ => ∫ u : ℝ in Set.Ioi 0,
      Real.exp (-s * u) * g (γ u.toNNReal)) atTop
      (𝓝 (∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g (γ u.toNNReal))) := tendsto_const_nhds
  have hlim := hc.sub hz
  have heq : (fun n : ℕ => ∫ u : ℝ in Set.Ioc (0 : ℝ) (n : ℝ),
      Real.exp (-s * u) * g (γ u.toNNReal)) =
      (fun n : ℕ => (∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) * g (γ u.toNNReal)) -
        Real.exp (-s * (n : ℝ)) * v n) := by
    funext n
    have h := u6_bounded_discounted_path_integral_split γ g hg B hb s hs (n : ℝ≥0)
    change (∫ u : ℝ in Set.Ioc (0 : ℝ) (n : ℝ), Real.exp (-s * u) * g (γ u.toNNReal)) +
      Real.exp (-s * (n : ℝ)) * v n = _ at h
    linarith
  rw [heq]
  simpa using hlim


/-- Truncated discounted expressions converge at every extended stopping time. -/
theorem u6_bounded_extended_discounted_expression_tendsto {d : ℕ} (γ : Path d)
    (g R : Vec d → ℝ) (hg : Measurable g) (B C : ℝ)
    (hb : ∀ y, |g y| ≤ B) (hR : ∀ y, ‖R y‖ ≤ C) (s : ℝ) (hs : 0 < s)
    (t : WithTop ℝ≥0) :
    Tendsto (fun n : ℕ =>
      let a : ℝ≥0 := WithTop.untopD 0 (min t ((n : ℝ≥0) : WithTop ℝ≥0))
      Real.exp (-s * (a : ℝ)) * R (γ a) +
        ∫ u : ℝ in Set.Ioc (0 : ℝ) (a : ℝ), Real.exp (-s * u) * g (γ u.toNNReal)) atTop
      (𝓝 ((if h : t = ⊤ then 0 else Real.exp (-s * (t.untop h : ℝ)) * R (γ (t.untop h))) +
        ∫ u : ℝ in {u | 0 < u ∧ (u.toNNReal : WithTop ℝ≥0) ≤ t},
          Real.exp (-s * u) * g (γ u.toNNReal))) := by
  cases t with
  | top =>
    have hz := u5_exp_discount_bounded_tendsto_zero s hs (fun n => R (γ (n : ℝ≥0))) C
      (fun n => hR _)
    have ho := u6_bounded_discounted_path_occupation_tendsto γ g hg B hb s hs
    simpa only [min_eq_right le_top, WithTop.untopD_coe, NNReal.coe_natCast, dif_pos rfl, dite_true,
      u5_extended_occupation_domain_top, zero_add] using hz.add ho
  | coe a =>
    have he := u5_extended_time_truncate_eventually a
    apply tendsto_const_nhds.congr'
    filter_upwards [he] with n hn
    rw [hn]
    simp only [WithTop.coe_ne_top, dite_false, WithTop.untop_coe,
      u5_extended_occupation_domain_coe]



/-- The bounded-observation discounted resolvent identity at a finite stopping time. -/
theorem u6_regular_signed_bounded_finite_stopped_discounted_resolvent
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : Vec d → ℝ) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ y, |g y| ≤ B)
    (T : Path d → ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (T γ : WithTop ℝ≥0)))
    :
    let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
    (∫ γ, (Real.exp (-s * (T γ : ℝ)) * R (γ (T γ)) +
      ∫ u : ℝ in Set.Ioc (0 : ℝ) (T γ : ℝ),
        Real.exp (-s * u) * g (γ u.toNNReal)) ∂K x) = R x := by
  let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
  let Φ : Path d → ℝ := fun η => ∫ t : ℝ in Set.Ioi 0, Real.exp (-s * t) * g (η t.toNNReal)
  let shift : Path d → Path d := fun γ => MarkovProcess.ContinuousPath.shift (T γ) γ
  let f : Path d → ℝ := fun γ => Φ (shift γ)
  let r : Path d → ℝ := fun γ => R (γ (T γ))
  let w : Path d → ℝ := fun γ => Real.exp (-s * (T γ : ℝ))
  have ht : Measurable[hT.measurableSpace] T := by
    simpa only [Function.comp_def, WithTop.untopD_coe] using (WithTop.measurable_untopD (0 : ℝ≥0)).comp hT.measurable
  have hw : StronglyMeasurable[hT.measurableSpace] w := by
    exact (Real.continuous_exp.measurable.comp
      (measurable_const.mul (NNReal.continuous_coe.measurable.comp ht))).stronglyMeasurable
  have hwm : AEStronglyMeasurable w (K x) :=
    (hw.mono hT.measurableSpace_le).aestronglyMeasurable
  have hwb : ∀ᵐ γ ∂K x, ‖w γ‖ ≤ 1 := ae_of_all _ fun γ => by
    rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
    exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hs.le) (NNReal.coe_nonneg (T γ)))
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hgm : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * g (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul
      (hg.comp heval)
  have hΦm : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hgm.stronglyMeasurable).measurable
  have hE : IntegrableOn (fun t : ℝ => B * Real.exp (-s * t)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul B
  have hbd (η : Path d) : ‖Φ η‖ ≤ ∫ t in Set.Ioi (0 : ℝ), B * Real.exp (-s * t) := by
    refine norm_integral_le_of_norm_le hE (ae_of_all _ fun t => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hb _)
      (Real.exp_nonneg _)
  have hΦ : Integrable Φ (K x) := by
    apply Integrable.of_bound hΦm.aestronglyMeasurable _
    exact ae_of_all _ hbd
  have hf : Integrable f (K x) := by
    apply Integrable.of_bound (hΦm.comp (MarkovProcess.ContinuousPath.measurable_shift_stoppingTime T hT)).aestronglyMeasurable _
    exact ae_of_all _ fun γ => hbd (shift γ)
  have hR := u6_regular_signed_discounted_bounded_observable_continuous
    hd ω lam Λ hΛ hω s hs g hg B hB hb
  have hr : Integrable r (K x) := by
    apply Integrable.of_bound (hR.1.measurable.comp
      (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel T hT)).aestronglyMeasurable (B / s)
    exact ae_of_all _ fun γ => by
      change |R (γ (T γ))| ≤ B / s
      exact hR.2 (γ (T γ))
  have hwf : Integrable (w * f) (K x) := hf.bdd_mul hwm hwb
  have hwr : Integrable (w * r) (K x) := hr.bdd_mul hwm hwb
  have hevent (A : Set (Path d)) (hA : MeasurableSet[hT.measurableSpace] A) :
      (∫ γ in A, f γ ∂K x) = ∫ γ in A, r γ ∂K x := by
    simpa only [f, r, Φ, shift, MarkovProcess.ContinuousPath.shift_apply] using
      u6_regular_signed_bounded_stopped_path_laplace hd ω lam Λ hΛ hω K hfdd
        x s hs g hg B hB hb T hT A hA
  have he : (∫ γ, (w * f) γ ∂K x) = ∫ γ, (w * r) γ ∂K x :=
    u5_integral_mul_of_setIntegral_eq hT.measurableSpace_le hf hr hw hwf hwr hevent
  have hpath : (∫ γ, Φ γ ∂K x) = R x := by
    exact u6_regular_signed_bounded_path_laplace hd ω lam Λ hΛ hω K hfdd x s hs g hg B hb
  change (∫ γ, (w * r) γ + (∫ u : ℝ in Set.Ioc (0 : ℝ) (T γ : ℝ),
    Real.exp (-s * u) * g (γ u.toNNReal)) ∂K x) = R x
  calc
    _ = ∫ γ, (Φ γ + (w * r) γ) - (w * f) γ ∂K x := by
      apply integral_congr_ae
      filter_upwards with γ
      have hp := u6_bounded_discounted_path_integral_split γ g hg B hb s hs (T γ)
      change (∫ u : ℝ in Set.Ioc (0 : ℝ) (T γ : ℝ),
        Real.exp (-s * u) * g (γ u.toNNReal)) + (w * f) γ = Φ γ at hp
      linarith
    _ = (∫ γ, Φ γ ∂K x) + (∫ γ, (w * r) γ ∂K x) -
        (∫ γ, (w * f) γ ∂K x) := by
      have hi := integral_sub (hΦ.add hwr) hwf
      simp only [Pi.add_apply] at hi
      rw [integral_add hΦ hwr] at hi
      exact hi
    _ = R x := by rw [he, hpath]; ring





/-- The bounded-observation resolvent identity at an extended stopping time. -/
theorem u6_regular_signed_bounded_extended_discounted_resolvent
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hfdd : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (x : Vec d) (s : ℝ) (hs : 0 < s)
    (g : Vec d → ℝ) (hg : Measurable g) (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ y, |g y| ≤ B) (T : Path d → WithTop ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) T) :
    let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
    (∫ γ, ((if h : T γ = ⊤ then 0 else
        Real.exp (-s * ((T γ).untop h : ℝ)) * R (γ ((T γ).untop h))) +
      ∫ u : ℝ in {u | 0 < u ∧ (u.toNNReal : WithTop ℝ≥0) ≤ T γ},
        Real.exp (-s*u) * g (γ u.toNNReal)) ∂K x) = R x := by
  dsimp only
  let R := u6RegularBoundedPhysicalResolvent hd ω lam Λ hΛ hω s g
  let A : ℕ → Path d → ℝ≥0 := fun n γ => WithTop.untopD 0
    (min (T γ) ((n : ℝ≥0) : WithTop ℝ≥0))
  have hA (n : ℕ) : IsStoppingTime
      (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d))
      (fun γ => (A n γ : WithTop ℝ≥0)) := u5_extended_stopping_time_truncate T hT _
  let Φ : Path d → ℝ := fun η => ∫ u : ℝ in Set.Ioi 0,
    Real.exp (-s * u) * g (η u.toNNReal)
  let D : ℝ := ∫ u : ℝ in Set.Ioi 0, B * Real.exp (-s * u)
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp (continuous_fst.prodMk
      (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hm : Measurable (fun z : Path d × ℝ => Real.exp (-s * z.2) * g (z.1 z.2.toNNReal)) :=
    (by fun_prop : Measurable fun z : Path d × ℝ => Real.exp (-s * z.2)).mul (hg.comp heval)
  have hΦm : Measurable Φ :=
    (StronglyMeasurable.integral_prod_right' (ν := volume.restrict (Set.Ioi (0 : ℝ)))
      hm.stronglyMeasurable).measurable
  have hE : IntegrableOn (fun u : ℝ => B * Real.exp (-s * u)) (Set.Ioi 0) :=
    (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).const_mul B
  have hΦb (η : Path d) : ‖Φ η‖ ≤ D := by
    refine norm_integral_le_of_norm_le hE (ae_of_all _ fun u => ?_)
    rw [norm_mul, Real.norm_of_nonneg (Real.exp_nonneg _), Real.norm_eq_abs, mul_comm]
    exact mul_le_mul_of_nonneg_right (hb _) (Real.exp_nonneg _)
  have hR := u6_regular_signed_discounted_bounded_observable_continuous
    hd ω lam Λ hΛ hω s hs g hg B hB hb
  have hRbound (y : Vec d) : ‖R y‖ ≤ B / s := by
    change |R y| ≤ B / s
    exact hR.2 y
  let F : ℕ → Path d → ℝ := fun n γ =>
    Real.exp (-s * (A n γ : ℝ)) * R (γ (A n γ)) +
      ∫ u : ℝ in Set.Ioc (0 : ℝ) (A n γ : ℝ), Real.exp (-s * u) * g (γ u.toNNReal)
  let G : Path d → ℝ := fun γ =>
    (if h : T γ = ⊤ then 0 else Real.exp (-s * ((T γ).untop h : ℝ)) * R (γ ((T γ).untop h))) +
      ∫ u : ℝ in {u | 0 < u ∧ (u.toNNReal : WithTop ℝ≥0) ≤ T γ},
        Real.exp (-s * u) * g (γ u.toNNReal)
  have hrepr (n : ℕ) (γ : Path d) : F n γ = Φ γ +
      Real.exp (-s * (A n γ : ℝ)) * R (γ (A n γ)) -
      Real.exp (-s * (A n γ : ℝ)) * Φ (MarkovProcess.ContinuousPath.shift (A n γ) γ) := by
    have hp := u6_bounded_discounted_path_integral_split γ g hg B hb s hs (A n γ)
    change (∫ u : ℝ in Set.Ioc (0 : ℝ) (A n γ : ℝ), Real.exp (-s * u) * g (γ u.toNNReal)) +
      Real.exp (-s * (A n γ : ℝ)) * Φ (MarkovProcess.ContinuousPath.shift (A n γ) γ) = Φ γ at hp
    dsimp only [F]
    linarith
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) (K x) := by
    have ht := MarkovProcess.ContinuousPath.measurable_of_isStoppingTime (A n) (hA n)
    have hw : Measurable (fun γ => Real.exp (-s * (A n γ : ℝ))) :=
      Real.continuous_exp.measurable.comp (measurable_const.mul (NNReal.continuous_coe.measurable.comp ht))
    have hr := hR.1.measurable.comp (MarkovProcess.ContinuousPath.measurable_eval_stoppingTime_borel (A n) (hA n))
    have hf := hΦm.comp (MarkovProcess.ContinuousPath.measurable_shift_stoppingTime (A n) (hA n))
    have h := (hΦm.add (hw.mul hr)).sub (hw.mul hf)
    have heq : F n = fun γ => Φ γ + Real.exp (-s * (A n γ : ℝ)) * R (γ (A n γ)) -
        Real.exp (-s * (A n γ : ℝ)) * Φ (MarkovProcess.ContinuousPath.shift (A n γ) γ) :=
      funext (hrepr n)
    rw [heq]
    exact h.aestronglyMeasurable
  have hbound (n : ℕ) (γ : Path d) : ‖F n γ‖ ≤ D + B / s + D := by
    have hw : ‖Real.exp (-s * (A n γ : ℝ))‖ ≤ 1 := by
      rw [Real.norm_of_nonneg (Real.exp_nonneg _)]
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg
        (neg_nonpos.mpr hs.le) (NNReal.coe_nonneg _))
    have hr : ‖Real.exp (-s * (A n γ : ℝ)) * R (γ (A n γ))‖ ≤ B / s := by
      rw [norm_mul]
      calc
        _ ≤ 1 * ‖R (γ (A n γ))‖ := mul_le_mul_of_nonneg_right hw (norm_nonneg _)
        _ ≤ B / s := by simpa only [one_mul] using hRbound (γ (A n γ))
    have hf : ‖Real.exp (-s * (A n γ : ℝ)) *
        Φ (MarkovProcess.ContinuousPath.shift (A n γ) γ)‖ ≤ D := by
      rw [norm_mul]
      calc
        _ ≤ 1 * ‖Φ (MarkovProcess.ContinuousPath.shift (A n γ) γ)‖ :=
          mul_le_mul_of_nonneg_right hw (norm_nonneg _)
        _ ≤ D := by simpa using hΦb (MarkovProcess.ContinuousPath.shift (A n γ) γ)
    rw [hrepr]
    exact (norm_sub_le _ _).trans ((add_le_add (norm_add_le _ _) le_rfl).trans
      (add_le_add (add_le_add (hΦb γ) hr) hf))
  have hlim (γ : Path d) : Tendsto (fun n => F n γ) atTop (𝓝 (G γ)) := by
    exact u6_bounded_extended_discounted_expression_tendsto γ g R hg B (B / s) hb
      hRbound s hs (T γ)
  have hconv := tendsto_integral_of_dominated_convergence (μ := K x) (fun _ => D + B / s + D)
    hFm (integrable_const _) (fun n => ae_of_all _ (hbound n)) (ae_of_all _ hlim)
  have heq (n : ℕ) : (∫ γ, F n γ ∂K x) = R x :=
    u6_regular_signed_bounded_finite_stopped_discounted_resolvent hd ω lam Λ hΛ hω
      K hfdd x s hs g hg B hB hb (A n) (hA n)
  have hc : Tendsto (fun n : ℕ => ∫ γ, F n γ ∂K x) atTop (𝓝 (R x)) := by
    simpa only [heq] using (tendsto_const_nhds : Tendsto (fun _ : ℕ => R x) atTop (𝓝 (R x)))
  exact tendsto_nhds_unique hconv hc



-- Path-law transport adapted from GMPRealizationUniqueness.lean.
private theorem continuous_list_getD {α : Type*} [TopologicalSpace α]
    (a₀ : α) (n : ℕ) : Continuous (fun l : List α => l[n]?.getD a₀) := by
  apply continuous_iff_continuousAt.mpr
  intro l
  induction l generalizing n with
  | nil =>
      rw [ContinuousAt, nhds_nil]
      exact tendsto_pure_nhds _ _
  | cons a l ih =>
      rw [ContinuousAt, List.tendsto_cons_iff]
      cases n with
      | zero => simpa only [List.getElem?_cons_zero, Option.getD_some] using tendsto_fst
      | succ n =>
          simpa only [List.getElem?_cons_succ, Function.comp_def] using Filter.Tendsto.comp (ih n) tendsto_snd

private theorem mem_pathEvalCylinder_iff {d : ℕ}
    (c : List (ℝ≥0 × Set (Vec d))) (γ : Path d) :
    γ ∈ pathEvalCylinder c ↔ ∀ p ∈ c, γ p.1 ∈ p.2 := by
  induction c with
  | nil => simp only [pathEvalCylinder, Set.mem_univ, List.not_mem_nil, false_implies,
      implies_true]
  | cons p c ih => simp only [pathEvalCylinder, Set.mem_inter_iff, Set.mem_setOf_eq,
      List.forall_mem_cons, ih]

private def positionCylinder {d : ℕ} (c : List (ℝ≥0 × Set (Vec d))) :
    Set (List (Vec d)) :=
  {ys | ∀ i : Fin c.length, ys[i.val]?.getD 0 ∈ (c[i.val]).2}

private theorem measurableSet_positionCylinder {d : ℕ}
    (c : List (ℝ≥0 × Set (Vec d))) (hc : ∀ p ∈ c, MeasurableSet p.2) :
    MeasurableSet (positionCylinder c) := by
  unfold positionCylinder
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro i
  exact (hc c[i.val] (List.getElem_mem i.isLt)).preimage
    (continuous_list_getD (0 : Vec d) i.val).measurable

private theorem positionCylinder_preimage {d : ℕ}
    (c : List (ℝ≥0 × Set (Vec d))) :
    (fun γ : Path d => pathPositionsAtTimes (c.map Prod.fst) γ) ⁻¹'
      positionCylinder c = pathEvalCylinder c := by
  ext γ
  rw [mem_pathEvalCylinder_iff]
  simp only [Set.mem_preimage, positionCylinder, Set.mem_setOf_eq,
    pathPositionsAtTimes, List.map_map, Function.comp_def, pathPosition]
  change (∀ i : Fin c.length,
    (c.map (fun p => γ p.1))[i.val]?.getD 0 ∈ (c[i.val]).2) ↔ _
  have hget (i : Fin c.length) :
      (c.map (fun p => γ p.1))[i.val]?.getD 0 = γ (c[i.val]).1 := by
    rw [List.getElem?_eq_getElem (by simpa only [List.length_map] using i.isLt),
      Option.getD_some, List.getElem_map]
  simp only [hget]
  simpa only [List.get_eq_getElem] using
    (List.forall_mem_iff_get (l := c) (p := fun p => γ p.1 ∈ p.2)).symm

private theorem exists_cumulativeTimesFrom {d : ℕ}
    (c : List (ℝ≥0 × Set (Vec d))) (s : ℝ≥0)
    (hs : ∀ p ∈ c, s ≤ p.1)
    (hc : c.Pairwise (fun p q => p.1 ≤ q.1)) :
    ∃ increments, cumulativeTimesFrom s increments = c.map Prod.fst := by
  induction c generalizing s with
  | nil => exact ⟨[], rfl⟩
  | cons p c ih =>
      obtain ⟨increments, hi⟩ := ih p.1
        (List.pairwise_cons.mp hc).1 (List.pairwise_cons.mp hc).2
      refine ⟨(p.1 - s) :: increments, ?_⟩
      simp only [cumulativeTimesFrom, add_tsub_cancel_of_le (hs p (by simp)),
        List.map_cons, hi]

private theorem cylinder_eq_of_ordered_integral_eq {d : ℕ}
    {P Q : Measure (Path d)} [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (h : ∀ (increments : List ℝ≥0) (F : List (Vec d) → ℝ),
      Measurable F → (∃ B : ℝ, ∀ z, |F z| ≤ B) →
        (∫ γ, F (pathPositionsAtTimes (cumulativeTimes increments) γ) ∂P) =
        ∫ γ, F (pathPositionsAtTimes (cumulativeTimes increments) γ) ∂Q)
    (c : List (ℝ≥0 × Set (Vec d))) (hc : ∀ p ∈ c, MeasurableSet p.2) :
    P (pathEvalCylinder c) = Q (pathEvalCylinder c) := by
  classical
  let c' := c.insertionSort (fun p q => p.1 ≤ q.1)
  have hperm : c'.Perm c := List.perm_insertionSort _ _
  have hc' : ∀ p ∈ c', MeasurableSet p.2 := fun p hp => hc p (hperm.mem_iff.mp hp)
  have hsorted : c'.Pairwise (fun p q => p.1 ≤ q.1) := by
    letI : @Std.Total (ℝ≥0 × Set (Vec d)) (fun p q => p.1 ≤ q.1) :=
      ⟨fun p q => le_total p.1 q.1⟩
    letI : IsTrans (ℝ≥0 × Set (Vec d)) (fun p q => p.1 ≤ q.1) :=
      ⟨fun _ _ _ hp hq => hp.trans hq⟩
    exact List.pairwise_insertionSort _ _
  obtain ⟨increments, hi⟩ := exists_cumulativeTimesFrom c' 0
    (fun p _ => bot_le) hsorted
  have hset : pathEvalCylinder c' = pathEvalCylinder c := by
    ext γ
    rw [mem_pathEvalCylinder_iff, mem_pathEvalCylinder_iff]
    constructor
    · intro h p hp
      exact h p (hperm.mem_iff.mpr hp)
    · intro h p hp
      exact h p (hperm.mem_iff.mp hp)
  let F : List (Vec d) → ℝ := (positionCylinder c').indicator 1
  have hFm : Measurable F := measurable_const.indicator (measurableSet_positionCylinder c' hc')
  have hFb : ∃ B : ℝ, ∀ z, |F z| ≤ B := by
    refine ⟨1, fun z => ?_⟩
    by_cases hz : z ∈ positionCylinder c' <;> simp [F, hz]
  have hpoint (γ : Path d) :
      F (pathPositionsAtTimes (cumulativeTimes increments) γ) =
        (pathEvalCylinder c).indicator (1 : Path d → ℝ) γ := by
    have hp : (fun γ : Path d => pathPositionsAtTimes (cumulativeTimes increments) γ) ⁻¹'
        positionCylinder c' = pathEvalCylinder c := by
      rw [cumulativeTimes, hi, positionCylinder_preimage, hset]
    change (positionCylinder c').indicator (fun _ => (1 : ℝ)) _ = _
    rw [← hp]
    rfl
  have heq := h increments F hFm hFb
  simp only [hpoint, integral_indicator_one (measurable_pathEvalCylinder c hc)] at heq
  exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top P _) (measure_ne_top Q _)).mp heq

/-- For the GMP laws of `paper/main.tex` 58–66 and 209–213, identical transition
kernels determine identical path laws through the ordered finite-dimensional fields. -/
private theorem u6_gmp_pathLaw_eq_of_transitionKernel_eq {d : ℕ} (hd : 2 ≤ d)
    (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀) (ω : FieldPair d) (hω : IsRegular Λ₀ ω)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r r' : GantertFixedEnvironmentRealization hd Λ₀ hΛ₀ ω hω lam h0 h1)
    (hK : r.transitionKernel = r'.transitionKernel) : r.pathLaw = r'.pathLaw := by
  apply Kernel.ext
  intro x
  letI : IsMarkovKernel r.pathLaw := r.pathLaw_isMarkovKernel
  letI : IsMarkovKernel r'.pathLaw := r'.pathLaw_isMarkovKernel
  apply measure_eq_of_eq_on_pathCylinders
  · apply cylinder_eq_of_ordered_integral_eq
    intro increments F hFm hFb
    rw [r.pathLaw_ordered_finite_dimensional increments x F hFm hFb,
      r'.pathLaw_ordered_finite_dimensional increments x F hFm hFb, hK]
  · simp only [measure_univ]


/-- Every supplied GMP transition kernel is the regular physical kernel at
every starting point. -/
theorem u6_arbitrary_supplied_gmp_transition_eq
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1) :
    ∀ t : ℝ≥0, r.transitionKernel t =
      (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t := by
  have hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ (volume : Measure (Vec d)) :=
    fun t ht => u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht
  obtain ⟨K, hKm, hfdd⟩ :=
    u6_regular_continuous_kernel_of_volume_ac hd ω lam Λ hΛ hω hac
  letI : IsMarkovKernel K := hKm
  obtain ⟨r', hr'K, hr'P⟩ :=
    u2_regular_fixed_environment_realization_of_ac_fdd hd ω lam Λ hΛ hω h0 h1 K hfdd hac
  have hae : ∀ t : ℝ≥0, 0 < t → ∀ f : ZeroAtInftyContinuousMap (Vec d) ℝ,
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        (∫ y, f y ∂r.transitionKernel t x) =
          ∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) t x := by
    intro t _ f
    have he := SbxS9RealizationUniqueness.transitionKernel_eq_ae hd hΛ r r' t
    have hv := (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp he
    filter_upwards [hv] with x hx
    rw [hx, hr'P]
  exact u5_supplied_gmp_transition_eq_of_ae_C0_action hd ω lam Λ hΛ hω h0 h1 r hae


/-- The finite-dimensional distributions of any supplied GMP realization agree
with those of the regular physical kernel at every starting point. -/
theorem u6_arbitrary_supplied_gmp_canonical_FDD
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1) :
    ∀ I : Finset ℝ≥0,
      r.pathLaw.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I := by
  have hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ (volume : Measure (Vec d)) :=
    fun t ht => u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht
  obtain ⟨K, hKm, hfdd⟩ :=
    u6_regular_continuous_kernel_of_volume_ac hd ω lam Λ hΛ hω hac
  letI : IsMarkovKernel K := hKm
  obtain ⟨r', hr'K, hr'P⟩ :=
    u2_regular_fixed_environment_realization_of_ac_fdd hd ω lam Λ hΛ hω h0 h1 K hfdd hac
  have hK : r.transitionKernel = fun t => u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t :=
    funext (u6_arbitrary_supplied_gmp_transition_eq hd ω lam Λ hΛ hω h0 h1 r)
  have hpaths : r.pathLaw = K := by
    rw [← hr'K]
    apply u6_gmp_pathLaw_eq_of_transitionKernel_eq hd Λ hΛ ω hω lam h0 h1 r r'
    exact hK.trans hr'P.symm
  intro I
  rw [hpaths]
  exact hfdd I



/-- The same supplied path law solves the physical martingale problem at
every starting point. -/
theorem u6_arbitrary_supplied_gmp_solves_martingale_problem
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1) (x : Vec d) :
    SolvesMartingaleProblem (physicalGenerator (firstCoordinateIndex hd) ω lam) x (r.pathLaw x) := by
  letI : IsMarkovKernel r.pathLaw := r.pathLaw_isMarkovKernel
  have hfdd := u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam Λ hΛ hω h0 h1 r
  have hac : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪ (volume : Measure (Vec d)) :=
    fun t ht => u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht
  exact (u2_regular_fixed_environment_realization_and_mp_of_ac_fdd
    hd ω lam Λ hΛ hω h0 h1 r.pathLaw hfdd hac).2 x


/-- Supplied GMP realizations in the same regular environment have the same
continuous path law at every starting point. -/
theorem u6_same_canonical_fdd_path_laws_equal
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r r' : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1) :
    r.pathLaw = r'.pathLaw := by
  apply u6_gmp_pathLaw_eq_of_transitionKernel_eq hd Λ hΛ ω hω lam h0 h1 r r'
  exact funext fun t =>
    (u6_arbitrary_supplied_gmp_transition_eq hd ω lam Λ hΛ hω h0 h1 r t).trans
      (u6_arbitrary_supplied_gmp_transition_eq hd ω lam Λ hΛ hω h0 h1 r' t).symm


/-- Any observable has the same law under supplied realizations in the same
regular environment. -/
theorem u6_supplied_observable_laws_equal
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r r' : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    {α : Type*} [MeasurableSpace α] (F : Path d → α) (x : Vec d) :
    (r.pathLaw x).map F = (r'.pathLaw x).map F := by
  rw [u6_same_canonical_fdd_path_laws_equal hd Λ hΛ ω hω lam h0 h1 r r']


/-- Every countable family of time evaluations has the same joint law under
supplied realizations in the same regular environment. -/
theorem u6_supplied_countable_time_laws_equal
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r r' : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (times : ℕ → ℝ≥0) (x : Vec d) :
    (r.pathLaw x).map (fun γ : Path d => fun n => γ (times n)) =
      (r'.pathLaw x).map (fun γ : Path d => fun n => γ (times n)) :=
  u6_supplied_observable_laws_equal hd Λ hΛ ω hω lam h0 h1 r r'
    (fun γ n => γ (times n)) x

/-- The stopped path observable has the same law for two supplied realizations
in one regular environment. -/
theorem u6_supplied_stopped_path_laws_equal
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r r' : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (U : Set (Vec d)) (x : Vec d) :
    (r.pathLaw x).map (Diffusion.localityStoppedPath U) =
      (r'.pathLaw x).map (Diffusion.localityStoppedPath U) :=
  u6_supplied_observable_laws_equal hd Λ hΛ ω hω lam h0 h1 r r'
    (Diffusion.localityStoppedPath U) x


/-- The positive-time occupation measure of the actual supplied GMP law is
absolutely continuous with respect to volume at every starting point. -/
theorem u6_arbitrary_supplied_gmp_occupation
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (x : Vec d) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      ((r.pathLaw x).prod (volume.restrict (Set.Ioi 0))) ≪
        (volume : Measure (Vec d)) := by
  letI : IsMarkovKernel r.pathLaw := r.pathLaw_isMarkovKernel
  apply u2_averaged_occupation_ac_of_marginals
  intro t ht
  rw [r.pathLaw_endpoint, u6_arbitrary_supplied_gmp_transition_eq hd ω lam Λ hΛ hω h0 h1 r t]
  exact u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht x


/-- Any two supplied GMP realizations have the same path law at every start. -/
theorem u6_arbitrary_supplied_gmp_pathLaw_unique
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G G' : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd L hL ω hω lam h0 h1) :
    ∀ x : Vec d, G.pathLaw x = G'.pathLaw x := by
  intro x
  exact congrArg (fun K => K x)
    (u6_same_canonical_fdd_path_laws_equal hd L hL ω hω lam h0 h1 G G')

end EinsteinFull
