import EinsteinFull.Calculus.U7RegularGaussianDensity
import EinsteinFull.Calculus.U4RegularKernelSmoothing
import EinsteinFull.Calculus.U6RegularPathResolvent
import EinsteinFull.Calculus.U6BoundedPhysicalResolvent
import EinsteinFull.Calculus.U1GMPEnvironmentAssembly
import EinsteinFull.Calculus.U1SignedStoppingRestartSupport
import MarkovProcess.Restart.ConditionalMarkov
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull

/-- Half-time averaging preserves joint time, start, and endpoint measurability. -/
theorem u1_half_time_kernel_average_measurable {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (p : ℝ≥0 → Vec d → Vec d → ℝ)
    (hp : Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2)) :
    Measurable (fun z : ℝ≥0 × Vec d × Vec d =>
      ∫ w, p (z.1 / 2) w z.2.2 ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
        (z.1 / 2) z.2.1) := by
  let K := (u6FullTimeKernel hd ω lam Λ hΛ hω).comap
    (fun z : ℝ≥0 × Vec d × Vec d => (z.1 / 2, z.2.1))
    (((continuous_fst.div_const 2).measurable).prodMk measurable_snd.fst)
  let : IsMarkovKernel K := ⟨fun z => ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω (z.1 / 2) z.2.1⟩⟩
  have hf : Measurable (fun z : (ℝ≥0 × Vec d × Vec d) × Vec d =>
      p (z.1.1 / 2) z.2 z.1.2.2) := by
    simpa only [Function.comp_def] using hp.comp
      (((continuous_fst.fst.div_const 2).measurable).prodMk
        (measurable_snd.prodMk measurable_fst.snd.snd))
  have h := hf.stronglyMeasurable.integral_kernel_prod_right' (κ := K)
  change StronglyMeasurable (fun z : ℝ≥0 × Vec d × Vec d =>
      ∫ w, p (z.1 / 2) w z.2.2 ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
        (z.1 / 2) z.2.1) at h
  exact h.measurable

#print axioms u1_half_time_kernel_average_measurable

/-- Pointwise continuous nonnegative unit-mass densities are continuous in L¹. -/
theorem u1_continuous_probability_density_rows_L1 {d : ℕ}
    (p : Vec d → Vec d → ℝ)
    (hp : ∀ x, Integrable (p x) volume)
    (hn : ∀ x y, 0 ≤ p x y)
    (hm : ∀ x, ∫ y, p x y = 1)
    (hc : ∀ y, Continuous (fun x => p x y)) (x : Vec d) :
    Tendsto (fun z : Vec d => ∫ y, |p z y - p x y|) (𝓝 x) (𝓝 0) := by
  let q : Vec d → Vec d → ℝ := fun z y => min (p z y) (p x y)
  have hq (z : Vec d) : Integrable (q z) volume := by
    apply (hp x).mono' (((hp z).aestronglyMeasurable.aemeasurable.min
      (hp x).aestronglyMeasurable.aemeasurable).aestronglyMeasurable)
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hn z y) (hn x y))]
    exact min_le_right _ _
  have hlim : Tendsto (fun z : Vec d => ∫ y, q z y) (𝓝 x) (𝓝 1) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (l := 𝓝 x) (F := q) (f := p x) (p x)
      (Filter.Eventually.of_forall fun z => (hq z).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hn z y) (hn x y))]
        exact min_le_right _ _) (hp x)
      (Filter.Eventually.of_forall fun y => by
        simpa only [q, min_self] using ((hc y).tendsto x).min
          (tendsto_const_nhds (x := p x y)))
    simpa [hm x] using h
  have heq (z : Vec d) : (∫ y, |p z y - p x y|) = 2 - 2 * ∫ y, q z y := by
    have hpoint (y : Vec d) : |p z y - p x y| = p z y + p x y - 2 * q z y := by
      dsimp [q]
      rcases le_total (p z y) (p x y) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    simp_rw [hpoint]
    change (∫ y, (p z + p x) y - (fun y => 2 * q z y) y) = _
    rw [integral_sub ((hp z).add (hp x)) ((hq z).const_mul 2)]
    simp only [Pi.add_apply]
    rw [integral_add (hp z) (hp x), integral_const_mul, hm z, hm x]
    ring
  simp_rw [heq]
  convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim) using 1; norm_num

#print axioms u1_continuous_probability_density_rows_L1

/-- Gaussian upper bounds make the actual half-time kernel average continuous. -/
theorem u1_gaussian_half_time_average_continuous {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (p : ℝ≥0 → Vec d → Vec d → ℝ)
    (hp : Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2))
    (hb : ∀ (t : ℝ≥0), 0 < t → ∀ x y,
      0 ≤ p t x y ∧ p t x y ≤
        C * (t : ℝ) ^ (-((d : ℝ) / 2)) *
          Real.exp (C * (t : ℝ) - c * ‖WithLp.toLp 2 (y - x)‖ ^ 2 / (t : ℝ)))
    (t : ℝ≥0) (ht : 0 < t) (y : Vec d) :
    Continuous (fun x => ∫ z, p (t / 2) z y ∂
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (t / 2) x) := by
  have hs : 0 < t / 2 := by positivity
  have hsreal : 0 < ((t / 2 : ℝ≥0) : ℝ) := by exact_mod_cast hs
  have hmeas : Measurable (fun z => p (t / 2) z y) := by
    simpa only [Function.comp_def, id_eq] using hp.comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  let B : ℝ := C * ((t / 2 : ℝ≥0) : ℝ) ^ (-((d : ℝ) / 2)) *
    Real.exp (C * ((t / 2 : ℝ≥0) : ℝ))
  have hbound (z : Vec d) : |p (t / 2) z y| ≤ B := by
    rw [abs_of_nonneg (hb (t / 2) hs z y).1]
    apply (hb (t / 2) hs z y).2.trans
    dsimp [B]
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    · positivity
    · apply sub_le_self
      positivity
  exact u4_regular_signed_kernel_strongFeller hd ω lam Λ hΛ hω (t / 2) hs
    (fun z => p (t / 2) z y) hmeas B hbound

#print axioms u1_gaussian_half_time_average_continuous

/-- Averaging bounded density sections gives the density of the composed kernel. -/
theorem u1_kernel_comp_average_density {d : ℕ}
    (K : Kernel (Vec d) (Vec d)) [IsMarkovKernel K]
    (p : Vec d → Vec d → ℝ) (hp : Measurable (Function.uncurry p))
    (hn : ∀ x y, 0 ≤ p x y)
    (hb : ∀ y, ∃ B : ℝ, ∀ x, |p x y| ≤ B)
    (hrep : ∀ x, K x = volume.withDensity (fun y => ENNReal.ofReal (p x y))) :
    ∀ x, (K.comp K) x = volume.withDensity
      (fun y => ENNReal.ofReal (∫ z, p z y ∂K x)) := by
  have hpm : Measurable (Function.uncurry (fun x y => ENNReal.ofReal (p x y))) :=
    hp.ennreal_ofReal
  have hcomp := (u7_kernel_comp_density volume K _ hpm hrep).2
  intro x
  rw [hcomp x]
  apply withDensity_congr_ae
  filter_upwards [] with y
  have hmy : Measurable (fun z => p z y) := hp.comp (measurable_id.prodMk measurable_const)
  obtain ⟨B, hB⟩ := hb y
  have hB0 : 0 ≤ B := (abs_nonneg (p 0 y)).trans (hB 0)
  have hi : Integrable (fun z => p z y) (K x) := by
    apply (integrable_const B).mono' hmy.aestronglyMeasurable
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs, Real.norm_of_nonneg hB0] using hB z
  have hmx : Measurable (fun z => ENNReal.ofReal (p x z)) :=
    (hp.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun z => hn z y),
    hrep x, lintegral_withDensity_eq_lintegral_mul volume hmx hmy.ennreal_ofReal]
  rfl

#print axioms u1_kernel_comp_average_density

theorem u1_regular_signed_kernel_continuous_density_rows
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ p : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) ∧
      (∀ t x y, 0 ≤ p t x y) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ x,
        Integrable (p t x) volume ∧ (∫ y, p t x y) = 1 ∧
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          volume.withDensity (fun y => ENNReal.ofReal (p t x y))) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ y, Continuous (fun x => p t x y)) ∧
      ∀ (t : ℝ≥0), 0 < t → ∀ x,
        Filter.Tendsto (fun z : Vec d => ∫ y, |p t z y - p t x y|)
          (𝓝 x) (𝓝 0) := by
  obtain ⟨C, c, q, hC, hc, hq, hb, hr⟩ :=
    u7_regular_signed_joint_gaussian_density hd ω lam Λ hΛ hω
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let p : ℝ≥0 → Vec d → Vec d → ℝ := fun t x y =>
    if t = 0 then 0 else ∫ z, q (t / 2) z y ∂P (t / 2) x
  have hp : Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) := by
    dsimp [p, P]
    exact measurable_const.piecewise (measurable_fst (measurableSet_singleton 0))
      (u1_half_time_kernel_average_measurable hd ω lam Λ hΛ hω q hq)
  have hn : ∀ t x y, 0 ≤ p t x y := by
    intro t x y
    by_cases ht : t = 0
    · simp [p, ht]
    · have hs : 0 < t / 2 := by positivity
      simp only [p, ht, ite_false]
      exact integral_nonneg fun z => (hb (t / 2) hs z y).1
  have hrows (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
      P t x = volume.withDensity (fun y => ENNReal.ofReal (p t x y)) := by
    let s := t / 2
    have hs : 0 < s := by dsimp [s]; positivity
    have hsreal : 0 < (s : ℝ) := by exact_mod_cast hs
    let K : Kernel (Vec d) (Vec d) := P s
    let : IsMarkovKernel K := ⟨fun z => ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω s z⟩⟩
    have hqm : Measurable (Function.uncurry (q s)) := by
      simpa only [Function.comp_def, Function.uncurry_def, id_eq] using
        hq.comp (measurable_const.prodMk measurable_id)
    have hbound (y : Vec d) : ∃ B : ℝ, ∀ z, |q s z y| ≤ B := by
      refine ⟨C * (s : ℝ) ^ (-((d : ℝ) / 2)) * Real.exp (C * (s : ℝ)), ?_⟩
      intro z
      rw [abs_of_nonneg (hb s hs z y).1]
      apply (hb s hs z y).2.trans
      apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
      · positivity
      · have : 0 ≤ c * ‖WithLp.toLp 2 (y - z)‖ ^ 2 / (s : ℝ) := by positivity
        linarith
    have hcomp := u1_kernel_comp_average_density K (q s) hqm
      (fun z y => (hb s hs z y).1) hbound (hr s hs) x
    have hadd : s + s = t := by dsimp [s]; exact add_halves t
    have heq : P t x = (K.comp K) x := by
      rw [← hadd, P.kernel_add]
    rw [heq, hcomp]
    simp only [p, ht.ne', ite_false, K, s]
  have hnorm (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
      Integrable (p t x) volume ∧ ∫ y, p t x y = 1 := by
    let K : Kernel (Vec d) (Vec d) := P t
    let : IsMarkovKernel K := ⟨fun z => ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t z⟩⟩
    have hm : Measurable (Function.uncurry (p t)) := by
      simpa only [Function.comp_def, Function.uncurry_def, id_eq] using hp.comp
        (measurable_const.prodMk measurable_id)
    exact u6_parameter_kernel_density_normalized K (p t) hm (hn t) (hrows t ht) x
  have hcont (t : ℝ≥0) (ht : 0 < t) (y : Vec d) : Continuous (fun x => p t x y) := by
    simpa only [p, ht.ne', ite_false, P] using
      u1_gaussian_half_time_average_continuous hd ω lam Λ hΛ hω C c hC hc q hq hb t ht y
  refine ⟨p, hp, hn, ?_, hcont, ?_⟩
  · intro t ht x
    exact ⟨(hnorm t ht x).1, (hnorm t ht x).2, hrows t ht x⟩
  · intro t ht x
    exact u1_continuous_probability_density_rows_L1 (p t) (fun z => (hnorm t ht z).1)
      (hn t) (fun z => (hnorm t ht z).2) (hcont t ht) x

#print axioms u1_regular_signed_kernel_continuous_density_rows


/-- Scheffé convergence for a continuous family of probability density rows. -/
theorem u1_continuous_probability_density_rows_L1_general {d : ℕ} {α : Type*} [TopologicalSpace α] [FirstCountableTopology α]
    (p : α → Vec d → ℝ)
    (hp : ∀ x, Integrable (p x) volume)
    (hn : ∀ x y, 0 ≤ p x y)
    (hm : ∀ x, ∫ y, p x y = 1)
    (x : α) (hc : ∀ y, ContinuousAt (fun x => p x y) x) :
    Tendsto (fun z : α => ∫ y, |p z y - p x y|) (𝓝 x) (𝓝 0) := by
  let q : α → Vec d → ℝ := fun z y => min (p z y) (p x y)
  have hq (z : α) : Integrable (q z) volume := by
    apply (hp x).mono' (((hp z).aestronglyMeasurable.aemeasurable.min
      (hp x).aestronglyMeasurable.aemeasurable).aestronglyMeasurable)
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hn z y) (hn x y))]
    exact min_le_right _ _
  have hlim : Tendsto (fun z : α => ∫ y, q z y) (𝓝 x) (𝓝 1) := by
    have h := tendsto_integral_filter_of_dominated_convergence (μ := volume)
      (l := 𝓝 x) (F := q) (f := p x) (p x)
      (Filter.Eventually.of_forall fun z => (hq z).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hn z y) (hn x y))]
        exact min_le_right _ _) (hp x)
      (Filter.Eventually.of_forall fun y => by
        simpa only [q, min_self] using (hc y).min
          (tendsto_const_nhds (x := p x y)))
    simpa [hm x] using h
  have heq (z : α) : (∫ y, |p z y - p x y|) = 2 - 2 * ∫ y, q z y := by
    have hpoint (y : Vec d) : |p z y - p x y| = p z y + p x y - 2 * q z y := by
      dsimp [q]
      rcases le_total (p z y) (p x y) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]
        ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]
        ring
    simp_rw [hpoint]
    change (∫ y, (p z + p x) y - (fun y => 2 * q z y) y) = _
    rw [integral_sub ((hp z).add (hp x)) ((hq z).const_mul 2)]
    simp only [Pi.add_apply]
    rw [integral_add (hp z) (hp x), integral_const_mul, hm z, hm x]
    ring
  simp_rw [heq]
  convert tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim) using 1; norm_num


#print axioms u1_continuous_probability_density_rows_L1_general


/-- The actual physical C₀ semigroup is jointly continuous in time and start. -/
theorem u1_regular_signed_c0_kernel_joint_continuous {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (f : ZeroAtInftyContinuousMap (Vec d) ℝ) :
    Continuous (fun z : ℝ≥0 × Vec d =>
      ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω z.1 z.2) := by
  simp_rw [u2RegularC0KernelSemigroup_integral]
  have h := ZeroAtInftyContinuousMap.isometry_toBCF.continuous.comp
    ((u2RegularC0Semigroup hd ω lam Λ hΛ hω).continuous_orbit f)
  exact (h.comp continuous_fst).eval continuous_snd

#print axioms u1_regular_signed_c0_kernel_joint_continuous


/-- A nonnegative bounded test dominated by a C₀ function has a C₀ kernel action. -/
theorem u1_regular_signed_kernel_action_c0_of_domination {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (f : Vec d → ℝ) (hf : Measurable f)
    (g : ZeroAtInftyContinuousMap (Vec d) ℝ)
    (hn : ∀ y, 0 ≤ f y) (hfg : ∀ y, f y ≤ g y) :
    Tendsto (fun x => ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)
      (cocompact (Vec d)) (𝓝 0) := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  have hgi (x : Vec d) : Integrable (fun y => g y) (P t x) := by
    let : IsProbabilityMeasure (P t x) := ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
    apply (integrable_const ‖g.toBCF‖).mono' g.continuous.aestronglyMeasurable
    filter_upwards [] with y
    exact g.toBCF.norm_coe_le_norm y
  have hfi (x : Vec d) : Integrable f (P t x) := by
    apply (hgi x).mono' hf.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_eq_abs, abs_of_nonneg (hn y)]
    exact hfg y
  apply squeeze_zero' (Filter.Eventually.of_forall fun x => integral_nonneg fun y => hn y)
  · exact Filter.Eventually.of_forall fun x => integral_mono (hfi x) (hgi x) hfg
  · simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω lam Λ hΛ hω t g).zero_at_infty'

#print axioms u1_regular_signed_kernel_action_c0_of_domination

/-- A centered Euclidean Gaussian vanishes at infinity. -/
theorem u1_endpoint_gaussian_tendsto_zero {d : ℕ} (a : ℝ) (ha : 0 < a)
    (y : Vec d) :
    Tendsto (fun x : Vec d => Real.exp (-a * euclideanNorm (y - x) ^ 2))
      (cocompact (Vec d)) (𝓝 0) := by
  have hn (v : Vec d) : ‖v‖ ≤ euclideanNorm v := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    apply Real.le_sqrt_of_sq_le
    rw [Real.norm_eq_abs, sq_abs]
    change v i ^ 2 ≤ ∑ j : Fin d, v j * v j
    simpa only [pow_two] using
      (Finset.single_le_sum (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i))
  have hbase : Tendsto (fun x : Vec d => ‖x‖ - ‖y‖)
      (cocompact (Vec d)) atTop := by
    simpa only [sub_eq_add_neg] using
      (tendsto_atTop_add_const_right _ (-‖y‖) tendsto_norm_cocompact_atTop)
  have hr : Tendsto (fun x : Vec d => euclideanNorm (y - x))
      (cocompact (Vec d)) atTop := by
    apply tendsto_atTop_mono (fun x => ?_) hbase
    have hh := norm_add_le (x - y) y
    rw [sub_add_cancel, norm_sub_rev] at hh
    linarith [hn (y - x)]
  have hs : Tendsto (fun x : Vec d => euclideanNorm (y - x) ^ 2)
      (cocompact (Vec d)) atTop := by
    simpa only [pow_two] using hr.atTop_mul_atTop₀ hr
  exact Real.tendsto_exp_atBot.comp (hs.const_mul_atTop_of_neg (neg_lt_zero.mpr ha))

#print axioms u1_endpoint_gaussian_tendsto_zero

/-- A Gaussian-dominated endpoint test becomes a C₀ function after positive-time smoothing. -/
theorem u1_regular_signed_gaussian_endpoint_c0 {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t)
    (f : Vec d → ℝ) (hf : Measurable f) (A a : ℝ)
    (hA : 0 ≤ A) (ha : 0 < a) (y : Vec d)
    (hn : ∀ x, 0 ≤ f x)
    (hbound : ∀ x, f x ≤ A * Real.exp (-a * euclideanNorm (y - x) ^ 2)) :
    ∃ g : ZeroAtInftyContinuousMap (Vec d) ℝ, ∀ x,
      g x = ∫ z, f z ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x := by
  have hc : Continuous (fun x : Vec d => A * Real.exp (-a * euclideanNorm (y - x) ^ 2)) := by
    exact continuous_const.mul (Real.continuous_exp.comp (continuous_const.mul
      (((EinsteinFull.Calculus.Feller.continuous_euclideanNorm d).comp
        (continuous_const.sub continuous_id)).pow 2)))
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ :=
    ⟨⟨_, hc⟩, by
      simpa only [mul_zero] using
        (tendsto_const_nhds.mul (u1_endpoint_gaussian_tendsto_zero a ha y))⟩
  have hB (x : Vec d) : |f x| ≤ A := by
    rw [abs_of_nonneg (hn x)]
    calc
      f x ≤ A * Real.exp (-a * euclideanNorm (y - x) ^ 2) := hbound x
      _ ≤ A * 1 := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha.le) (sq_nonneg _))) hA
      _ = A := mul_one A
  let G : ZeroAtInftyContinuousMap (Vec d) ℝ :=
    ⟨⟨_, u4_regular_signed_kernel_strongFeller hd ω lam Λ hΛ hω t ht f hf A hB⟩,
      u1_regular_signed_kernel_action_c0_of_domination hd ω lam Λ hΛ hω t f hf g hn hbound⟩
  exact ⟨G, fun _ => rfl⟩

#print axioms u1_regular_signed_gaussian_endpoint_c0

/-- Two density kernels compose by integrating the later density against the earlier kernel. -/
theorem u1_kernel_comp_average_density_two {d : ℕ}
    (K L : Kernel (Vec d) (Vec d)) [IsMarkovKernel K]
    (p q : Vec d → Vec d → ℝ) (hp : Measurable (Function.uncurry p))
    (hq : Measurable (Function.uncurry q))
    (hn : ∀ x y, 0 ≤ q x y)
    (hb : ∀ y, ∃ B : ℝ, ∀ x, |q x y| ≤ B)
    (hK : ∀ x, K x = volume.withDensity (fun y => ENNReal.ofReal (p x y)))
    (hL : ∀ x, L x = volume.withDensity (fun y => ENNReal.ofReal (q x y))) :
    ∀ x, (L.comp K) x = volume.withDensity
      (fun y => ENNReal.ofReal (∫ z, q z y ∂K x)) := by
  have hpm : Measurable (Function.uncurry (fun x y => ENNReal.ofReal (p x y))) := hp.ennreal_ofReal
  have hqm : Measurable (Function.uncurry (fun x y => ENNReal.ofReal (q x y))) := hq.ennreal_ofReal
  have hconv (x : Vec d) : (L.comp K) x = volume.withDensity
      (fun y => ∫⁻ z, ENNReal.ofReal (p x z) * ENNReal.ofReal (q z y) ∂volume) := by
    have hpx : Measurable (fun z => ENNReal.ofReal (p x z)) :=
      (hp.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
    ext s hs
    rw [Kernel.comp_apply' L K x hs, hK x,
      lintegral_withDensity_eq_lintegral_mul volume hpx (Kernel.measurable_coe L hs),
      withDensity_apply _ hs]
    simp_rw [hL, withDensity_apply _ hs]
    have hprod : Measurable (fun w : Vec d × Vec d => ENNReal.ofReal (p x w.1) *
        ENNReal.ofReal (q w.1 w.2)) :=
      ((hpm.comp (measurable_const.prodMk measurable_id)).comp measurable_fst).mul hqm
    calc
      _ = ∫⁻ z, ∫⁻ y in s, ENNReal.ofReal (p x z) * ENNReal.ofReal (q z y) ∂volume ∂volume := by
        apply lintegral_congr
        intro z
        exact (lintegral_const_mul (ENNReal.ofReal (p x z))
          (hqm.comp (measurable_const.prodMk measurable_id))).symm
      _ = ∫⁻ y in s, ∫⁻ z, ENNReal.ofReal (p x z) * ENNReal.ofReal (q z y) ∂volume ∂volume :=
        lintegral_lintegral_swap hprod.aemeasurable
  intro x
  rw [hconv x]
  apply withDensity_congr_ae
  filter_upwards [] with y
  have hmy : Measurable (fun z => q z y) := hq.comp (measurable_id.prodMk measurable_const)
  obtain ⟨B, hB⟩ := hb y
  have hB0 : 0 ≤ B := (abs_nonneg (q 0 y)).trans (hB 0)
  have hi : Integrable (fun z => q z y) (K x) := by
    apply (integrable_const B).mono' hmy.aestronglyMeasurable
    filter_upwards [] with z
    simpa only [Real.norm_eq_abs, Real.norm_of_nonneg hB0] using hB z
  have hmx : Measurable (fun z => ENNReal.ofReal (p x z)) :=
    (hp.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun z => hn z y),
    hK x, lintegral_withDensity_eq_lintegral_mul volume hmx hmy.ennreal_ofReal]
  rfl

#print axioms u1_kernel_comp_average_density_two

/-- A fixed endpoint section of the actual Gaussian row smooths into C₀. -/
theorem u1_regular_signed_actual_gaussian_endpoint_c0 {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (p : ℝ≥0 → Vec d → Vec d → ℝ)
    (hp : Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2))
    (hb : ∀ (t : ℝ≥0), 0 < t → ∀ x y,
      0 ≤ p t x y ∧ p t x y ≤
        C * (t : ℝ) ^ (-((d : ℝ) / 2)) *
          Real.exp (C * (t : ℝ) - c * ‖WithLp.toLp 2 (y - x)‖ ^ 2 / (t : ℝ)))
    (s : ℝ≥0) (hs : 0 < s) (y : Vec d) :
    ∃ g : ZeroAtInftyContinuousMap (Vec d) ℝ, ∀ x,
      g x = ∫ z, p s z y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s x := by
  have hsreal : 0 < (s : ℝ) := by exact_mod_cast hs
  have hm : Measurable (fun z => p s z y) := by
    simpa only [Function.comp_def, id_eq] using hp.comp
      (measurable_const.prodMk (measurable_id.prodMk measurable_const))
  let A : ℝ := C * (s : ℝ) ^ (-((d : ℝ) / 2)) * Real.exp (C * (s : ℝ))
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have ha : 0 < c / (s : ℝ) := div_pos hc hsreal
  apply u1_regular_signed_gaussian_endpoint_c0 hd ω lam Λ hΛ hω s hs
    (fun z => p s z y) hm A (c / (s : ℝ)) hA ha y
    (fun z => (hb s hs z y).1)
  intro z
  apply (hb s hs z y).2.trans_eq
  dsimp [A]
  simp only [TimeChange.euclideanNorm_eq_norm_toLp, mul_assoc, ← Real.exp_add]
  congr 2
  apply congrArg Real.exp
  simp only [WithLp.toLp_sub]
  ring

#print axioms u1_regular_signed_actual_gaussian_endpoint_c0

/-- The fixed-split Gaussian row is jointly continuous in the remaining time and start. -/
theorem u1_regular_signed_fixed_split_joint_continuous {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (p : ℝ≥0 → Vec d → Vec d → ℝ)
    (hp : Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2))
    (hb : ∀ (t : ℝ≥0), 0 < t → ∀ x y,
      0 ≤ p t x y ∧ p t x y ≤
        C * (t : ℝ) ^ (-((d : ℝ) / 2)) *
          Real.exp (C * (t : ℝ) - c * ‖WithLp.toLp 2 (y - x)‖ ^ 2 / (t : ℝ)))
    (s : ℝ≥0) (hs : 0 < s) (y : Vec d) :
    Continuous (fun w : ℝ≥0 × Vec d => ∫ z,
      (∫ v, p s v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω w.1 w.2) := by
  obtain ⟨g, hg⟩ := u1_regular_signed_actual_gaussian_endpoint_c0
    hd ω lam Λ hΛ hω C c hC hc p hp hb s hs y
  simpa only [← hg] using
    u1_regular_signed_c0_kernel_joint_continuous hd ω lam Λ hΛ hω g

#print axioms u1_regular_signed_fixed_split_joint_continuous

/-- Fixed-time averaging of the joint density remains jointly measurable. -/
theorem u1_fixed_time_kernel_average_measurable {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (p : ℝ≥0 → Vec d → Vec d → ℝ)
    (hp : Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2))
    (s : ℝ≥0) :
    Measurable (Function.uncurry (fun x y =>
      ∫ z, p s z y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s x)) := by
  have hh : (s + s) / 2 = s := by rw [add_div, add_halves]
  have hk : Measurable (fun z : Vec d × Vec d => (s + s, z)) :=
    measurable_const.prodMk measurable_id
  have h := (u1_half_time_kernel_average_measurable hd ω lam Λ hΛ hω p hp).comp hk
  simpa only [Function.comp_def, Function.uncurry_def, id_eq, hh] using h

#print axioms u1_fixed_time_kernel_average_measurable

/-- The fixed-split row is the actual kernel density at the sum of the times. -/
theorem u1_regular_signed_fixed_split_density {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (p : ℝ≥0 → Vec d → Vec d → ℝ)
    (hp : Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2))
    (hb : ∀ (t : ℝ≥0), 0 < t → ∀ x y,
      0 ≤ p t x y ∧ p t x y ≤
        C * (t : ℝ) ^ (-((d : ℝ) / 2)) *
          Real.exp (C * (t : ℝ) - c * ‖WithLp.toLp 2 (y - x)‖ ^ 2 / (t : ℝ)))
    (hr : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (p t x y)))
    (s : ℝ≥0) (hs : 0 < s) (r : ℝ≥0) (hrpos : 0 < r) (x : Vec d) :
    u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (r + (s + s)) x =
      volume.withDensity (fun y => ENNReal.ofReal (∫ z,
        (∫ v, p s v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
          ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x)) := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let q : Vec d → Vec d → ℝ := fun z y => ∫ v, p s v y ∂P s z
  let : IsMarkovKernel (P s) := ⟨fun z => ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω s z⟩⟩
  let : IsMarkovKernel (P r) := ⟨fun z => ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω r z⟩⟩
  have hpm (t : ℝ≥0) : Measurable (Function.uncurry (p t)) := by
    simpa only [Function.comp_def, Function.uncurry_def, id_eq] using
      hp.comp (measurable_const.prodMk measurable_id)
  have hqm : Measurable (Function.uncurry q) :=
    u1_fixed_time_kernel_average_measurable hd ω lam Λ hΛ hω p hp s
  have hpn : ∀ z y, 0 ≤ p s z y := fun z y => (hb s hs z y).1
  have hpb (y : Vec d) : ∃ B : ℝ, ∀ z, |p s z y| ≤ B := by
    have hsreal : 0 < (s : ℝ) := by exact_mod_cast hs
    refine ⟨C * (s : ℝ) ^ (-((d : ℝ) / 2)) * Real.exp (C * (s : ℝ)), ?_⟩
    intro z
    rw [abs_of_nonneg (hpn z y)]
    apply (hb s hs z y).2.trans
    apply mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    · positivity
    · have : 0 ≤ c * ‖WithLp.toLp 2 (y - z)‖ ^ 2 / (s : ℝ) := by positivity
      linarith
  have hqn (z y : Vec d) : 0 ≤ q z y := integral_nonneg fun v => hpn v y
  have hqb (y : Vec d) : ∃ B : ℝ, ∀ z, |q z y| ≤ B := by
    obtain ⟨g, hg⟩ := u1_regular_signed_actual_gaussian_endpoint_c0
      hd ω lam Λ hΛ hω C c hC hc p hp hb s hs y
    refine ⟨‖g.toBCF‖, ?_⟩
    intro z
    change |(∫ v, p s v y ∂P s z)| ≤ ‖g.toBCF‖
    rw [← hg z, ← Real.norm_eq_abs]
    exact g.toBCF.norm_coe_le_norm z
  have hqrep (z : Vec d) : P (s + s) z = volume.withDensity (fun y => ENNReal.ofReal (q z y)) := by
    rw [P.kernel_add]
    exact u1_kernel_comp_average_density (P s) (p s) (hpm s) hpn hpb (hr s hs) z
  have heq := u1_kernel_comp_average_density_two (P r) (P (s + s)) (p r) q
    (hpm r) hqm hqn hqb (hr r hrpos) hqrep x
  rw [P.kernel_add]
  exact heq

#print axioms u1_regular_signed_fixed_split_density

/-- Nonnegative measurable real densities for the same measure agree almost everywhere. -/
theorem u1_nonnegative_density_ae_eq {d : ℕ} (f g : Vec d → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hnf : ∀ y, 0 ≤ f y) (hng : ∀ y, 0 ≤ g y)
    (heq : volume.withDensity (fun y => ENNReal.ofReal (f y)) =
      volume.withDensity (fun y => ENNReal.ofReal (g y))) :
    f =ᵐ[volume] g := by
  have hae := (withDensity_eq_iff_of_sigmaFinite hf.ennreal_ofReal.aemeasurable
    hg.ennreal_ofReal.aemeasurable).mp heq
  filter_upwards [hae] with y hy
  simpa only [ENNReal.toReal_ofReal (hnf y), ENNReal.toReal_ofReal (hng y)] using
    congrArg ENNReal.toReal hy

#print axioms u1_nonnegative_density_ae_eq

/-- Fixed-split averaging is jointly measurable in time, start, and endpoint. -/
theorem u1_fixed_split_kernel_average_measurable {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (p : ℝ≥0 → Vec d → Vec d → ℝ)
    (hp : Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2))
    (s : ℝ≥0) :
    Measurable (fun w : ℝ≥0 × Vec d × Vec d => ∫ z,
      (∫ v, p s v w.2.2 ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω w.1 w.2.1) := by
  have hk : Measurable (fun w : ℝ≥0 × Vec d × Vec d => (w.1, w.2.1)) := by
    exact measurable_fst.prodMk measurable_snd.fst
  let K := (u6FullTimeKernel hd ω lam Λ hΛ hω).comap
    (fun w : ℝ≥0 × Vec d × Vec d => (w.1, w.2.1)) hk
  let : IsMarkovKernel K := ⟨fun w => ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω w.1 w.2.1⟩⟩
  have hq := u1_fixed_time_kernel_average_measurable hd ω lam Λ hΛ hω p hp s
  have hf : Measurable (fun w : (ℝ≥0 × Vec d × Vec d) × Vec d =>
      ∫ v, p s v w.1.2.2 ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s w.2) := by
    simpa only [Function.comp_def, Function.uncurry_def] using
      hq.comp (measurable_snd.prodMk measurable_fst.snd.snd)
  have h := hf.stronglyMeasurable.integral_kernel_prod_right' (κ := K)
  change StronglyMeasurable (fun w : ℝ≥0 × Vec d × Vec d => ∫ z,
      (∫ v, p s v w.2.2 ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω w.1 w.2.1) at h
  exact h.measurable

#print axioms u1_fixed_split_kernel_average_measurable


/-- A positive-time fixed-split row is an integrable probability density. -/
theorem u1_regular_signed_fixed_split_normalized {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (q : ℝ≥0 → Vec d → Vec d → ℝ)
    (hq : Measurable (fun z : ℝ≥0 × Vec d × Vec d => q z.1 z.2.1 z.2.2))
    (hb : ∀ (t : ℝ≥0), 0 < t → ∀ x y,
      0 ≤ q t x y ∧ q t x y ≤
        C * (t : ℝ) ^ (-((d : ℝ) / 2)) *
          Real.exp (C * (t : ℝ) - c * ‖WithLp.toLp 2 (y - x)‖ ^ 2 / (t : ℝ)))
    (hr : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (q t x y)))
    (s : ℝ≥0) (hs : 0 < s) (r : ℝ≥0) (hrpos : 0 < r) (x : Vec d) :
    Integrable (fun y => ∫ z,
      (∫ v, q s v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x) volume ∧
    (∫ y, ∫ z,
      (∫ v, q s v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x) = 1 := by
  obtain ⟨p, hp, hn, hrows, _, _⟩ :=
    u1_regular_signed_kernel_continuous_density_rows hd ω lam Λ hΛ hω
  let f : Vec d → ℝ := fun y => ∫ z,
    (∫ v, q s v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
      ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x
  have ht : 0 < r + (s + s) := by positivity
  have hpm : Measurable (p (r + (s + s)) x) := by
    have hmap : Measurable (fun y : Vec d => (r + (s + s), x, y)) :=
      measurable_const.prodMk (measurable_const.prodMk measurable_id)
    exact hp.comp hmap
  have hfm : Measurable f := by
    have hmap : Measurable (fun y : Vec d => (r, x, y)) :=
      measurable_const.prodMk (measurable_const.prodMk measurable_id)
    simpa only [f, Function.comp_def] using
      (u1_fixed_split_kernel_average_measurable hd ω lam Λ hΛ hω q hq s).comp hmap
  have hfn : ∀ y, 0 ≤ f y := fun y =>
    integral_nonneg fun z => integral_nonneg fun v => (hb s hs v y).1
  have heq : p (r + (s + s)) x =ᵐ[volume] f :=
    u1_nonnegative_density_ae_eq _ _ hpm hfm (hn _ _) hfn
      ((hrows _ ht x).2.2.symm.trans
        (u1_regular_signed_fixed_split_density hd ω lam Λ hΛ hω C c hC hc
          q hq hb hr s hs r hrpos x))
  exact ⟨(hrows _ ht x).1.congr heq, (integral_congr_ae heq).symm.trans (hrows _ ht x).2.1⟩

#print axioms u1_regular_signed_fixed_split_normalized

/-- Fixed-split probability rows vary continuously in positive time and start in L1. -/
theorem u1_regular_signed_fixed_split_L1 {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (q : ℝ≥0 → Vec d → Vec d → ℝ)
    (hq : Measurable (fun z : ℝ≥0 × Vec d × Vec d => q z.1 z.2.1 z.2.2))
    (hb : ∀ (t : ℝ≥0), 0 < t → ∀ x y,
      0 ≤ q t x y ∧ q t x y ≤
        C * (t : ℝ) ^ (-((d : ℝ) / 2)) *
          Real.exp (C * (t : ℝ) - c * ‖WithLp.toLp 2 (y - x)‖ ^ 2 / (t : ℝ)))
    (hr : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (q t x y)))
    (s : ℝ≥0) (hs : 0 < s) (r : {t : ℝ≥0 // 0 < t}) (x : Vec d) :
    Filter.Tendsto (fun w : {t : ℝ≥0 // 0 < t} × Vec d => ∫ y,
      |(∫ z, (∫ v, q s v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
          ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω w.1.1 w.2) -
        (∫ z, (∫ v, q s v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
          ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r.1 x)|)
      (𝓝 (r, x)) (𝓝 0) := by
  let f : ({t : ℝ≥0 // 0 < t} × Vec d) → Vec d → ℝ := fun w y => ∫ z,
    (∫ v, q s v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
      ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω w.1.1 w.2
  have hnorm (w : {t : ℝ≥0 // 0 < t} × Vec d) :=
    u1_regular_signed_fixed_split_normalized hd ω lam Λ hΛ hω C c hC hc
      q hq hb hr s hs w.1.1 w.1.2 w.2
  have hn (w : {t : ℝ≥0 // 0 < t} × Vec d) (y : Vec d) : 0 ≤ f w y :=
    integral_nonneg fun z => integral_nonneg fun v => (hb s hs v y).1
  have hcont (y : Vec d) : ContinuousAt (fun w => f w y) (r, x) := by
    have hm : Continuous (fun w : {t : ℝ≥0 // 0 < t} × Vec d => (w.1.1, w.2)) :=
      (continuous_subtype_val.comp continuous_fst).prodMk continuous_snd
    exact ((u1_regular_signed_fixed_split_joint_continuous hd ω lam Λ hΛ hω
      C c hC hc q hq hb s hs y).comp hm).continuousAt
  exact u1_continuous_probability_density_rows_L1_general f
    (fun w => (hnorm w).1) hn (fun w => (hnorm w).2) (r, x) hcont

#print axioms u1_regular_signed_fixed_split_L1

/-- The chosen actual density agrees almost everywhere with every positive fixed split. -/
theorem u1_regular_signed_fixed_split_row_ae {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (p : ℝ≥0 → Vec d → Vec d → ℝ)
    (hp : Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2))
    (hn : ∀ t x y, 0 ≤ p t x y)
    (hrows : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      Integrable (p t x) volume ∧ (∫ y, p t x y) = 1 ∧
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          volume.withDensity (fun y => ENNReal.ofReal (p t x y)))
    (C c : ℝ) (hC : 0 < C) (hc : 0 < c)
    (q : ℝ≥0 → Vec d → Vec d → ℝ)
    (hq : Measurable (fun z : ℝ≥0 × Vec d × Vec d => q z.1 z.2.1 z.2.2))
    (hb : ∀ (t : ℝ≥0), 0 < t → ∀ x y,
      0 ≤ q t x y ∧ q t x y ≤
        C * (t : ℝ) ^ (-((d : ℝ) / 2)) *
          Real.exp (C * (t : ℝ) - c * ‖WithLp.toLp 2 (y - x)‖ ^ 2 / (t : ℝ)))
    (hr : ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (q t x y)))
    (s : ℝ≥0) (hs : 0 < s) (r : ℝ≥0) (hrpos : 0 < r) (x : Vec d) :
    p (r + (s + s)) x =ᵐ[volume] fun y => ∫ z,
      (∫ v, q s v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x := by
  let f : Vec d → ℝ := fun y => ∫ z,
    (∫ v, q s v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
      ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r x
  have ht : 0 < r + (s + s) := by positivity
  have hpm : Measurable (p (r + (s + s)) x) := by
    have hmap : Measurable (fun y : Vec d => (r + (s + s), x, y)) :=
      measurable_const.prodMk (measurable_const.prodMk measurable_id)
    exact hp.comp hmap
  have hfm : Measurable f := by
    have hmap : Measurable (fun y : Vec d => (r, x, y)) :=
      measurable_const.prodMk (measurable_const.prodMk measurable_id)
    simpa only [f, Function.comp_def] using
      (u1_fixed_split_kernel_average_measurable hd ω lam Λ hΛ hω q hq s).comp hmap
  have hfn : ∀ y, 0 ≤ f y := fun y =>
    integral_nonneg fun z => integral_nonneg fun v => (hb s hs v y).1
  exact u1_nonnegative_density_ae_eq _ _ hpm hfm (hn _ _) hfn
    ((hrows _ ht x).2.2.symm.trans
      (u1_regular_signed_fixed_split_density hd ω lam Λ hΛ hω C c hC hc
        q hq hb hr s hs r hrpos x))

#print axioms u1_regular_signed_fixed_split_row_ae

/-- Actual positive-time kernel rows are jointly continuous in total variation. -/
theorem u1_regular_signed_kernel_joint_L1_row_continuity
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ p : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => p z.1 z.2.1 z.2.2) ∧
      (∀ t x y, 0 ≤ p t x y) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ x,
        Integrable (p t x) volume ∧ (∫ y, p t x y) = 1 ∧
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          volume.withDensity (fun y => ENNReal.ofReal (p t x y))) ∧
      ∀ (t : ℝ≥0), 0 < t → ∀ x,
        Filter.Tendsto (fun z : ℝ≥0 × Vec d => ∫ y, |p z.1 z.2 y - p t x y|)
          (𝓝 (t, x)) (𝓝 0) := by
  obtain ⟨p, hp, hn, hrows, _, _⟩ :=
    u1_regular_signed_kernel_continuous_density_rows hd ω lam Λ hΛ hω
  obtain ⟨C, c, q, hC, hc, hq, hb, hr⟩ :=
    u7_regular_signed_joint_gaussian_density hd ω lam Λ hΛ hω
  refine ⟨p, hp, hn, hrows, ?_⟩
  intro t ht x
  let s : ℝ≥0 := t / 4
  have hs : 0 < s := by dsimp [s]; positivity
  have hsmall : s + s < t := by
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have hh : ((s + s : ℝ≥0) : ℝ) < (t : ℝ) := by
      dsimp [s]
      push_cast
      linarith
    exact_mod_cast hh
  let r : {u : ℝ≥0 // 0 < u} := ⟨t - (s + s), tsub_pos_of_lt hsmall⟩
  let g : ℝ≥0 → {u : ℝ≥0 // 0 < u} := fun u =>
    if h : s + s < u then ⟨u - (s + s), tsub_pos_of_lt h⟩ else r
  have hgt : g t = r := by simp [g, r, hsmall]
  have hg : Tendsto g (𝓝 t) (𝓝 r) := by
    apply tendsto_subtype_rng.mpr
    have hcont : Tendsto (fun u : ℝ≥0 => u - (s + s)) (𝓝 t) (𝓝 (t - (s + s))) :=
      (continuous_id.sub continuous_const).continuousAt
    apply hcont.congr'
    filter_upwards [eventually_gt_nhds hsmall] with u hu
    simp [g, hu]
  have hf : Tendsto (fun w : ℝ≥0 × Vec d => w.1) (𝓝 (t, x)) (𝓝 t) :=
    continuous_fst.continuousAt
  have hx : Tendsto (fun w : ℝ≥0 × Vec d => w.2) (𝓝 (t, x)) (𝓝 x) :=
    continuous_snd.continuousAt
  have hmap : Tendsto (fun w : ℝ≥0 × Vec d => (g w.1, w.2))
      (𝓝 (t, x)) (𝓝 (r, x)) := by
    simpa only [Function.comp_def, nhds_prod_eq] using (hg.comp hf).prodMk hx
  have hlim := (u1_regular_signed_fixed_split_L1 hd ω lam Λ hΛ hω C c hC hc
    q hq hb hr s hs r x).comp hmap
  have hbase := u1_regular_signed_fixed_split_row_ae hd ω lam Λ hΛ hω p hp hn hrows
    C c hC hc q hq hb hr s hs r.1 r.2 x
  have hbase' : p t x =ᵐ[volume] fun y => ∫ z,
      (∫ v, q s v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω r.1 x := by
    simpa only [r, tsub_add_cancel_of_le hsmall.le] using hbase
  apply hlim.congr'
  filter_upwards [hf.eventually (eventually_gt_nhds hsmall)] with w hw
  have hwpos : 0 < w.1 - (s + s) := tsub_pos_of_lt hw
  have hwrow := u1_regular_signed_fixed_split_row_ae hd ω lam Λ hΛ hω p hp hn hrows
    C c hC hc q hq hb hr s hs (w.1 - (s + s)) hwpos w.2
  have hwrow' : p w.1 w.2 =ᵐ[volume] fun y => ∫ z,
      (∫ v, q s v y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω s z)
        ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω (g w.1).1 w.2 := by
    simpa only [g, dif_pos hw, tsub_add_cancel_of_le hw.le] using hwrow
  apply integral_congr_ae
  filter_upwards [hwrow', hbase'] with y hy hz
  rw [hy, hz]

#print axioms u1_regular_signed_kernel_joint_L1_row_continuity


/-- A continuous representative of an actual reversible kernel is symmetric
at every pair of points. -/
theorem u1_regular_continuous_reversible_density_symmetric
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0)
    (p : Vec d → Vec d → ℝ) (hp : Continuous (Function.uncurry p))
    (hn : ∀ x y, 0 ≤ p x y)
    (hr : ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
      (physicalReversibleMeasure ω hd lam).withDensity (fun y => ENNReal.ofReal (p x y))) :
    ∀ x y, p x y = p y x := by
  let : SigmaFinite (physicalReversibleMeasure ω hd lam) :=
    EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  have hae := u6_regular_kernel_density_symmetric hd ω lam Λ hΛ hω t p hp.measurable hn hr
  have hac : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd lam :=
    Blueprint.gmpVolume_absolutelyContinuous_physical hd ω lam
  have hvol : (fun z : Vec d × Vec d => p z.1 z.2) =ᵐ[volume]
      (fun z : Vec d × Vec d => p z.2 z.1) := by
    exact (hac.prod hac).ae_eq hae
  have heq := Measure.eq_of_ae_eq hvol hp (hp.comp continuous_swap)
  intro x y
  exact congrFun heq (x, y)

#print axioms u1_regular_continuous_reversible_density_symmetric


/-- The selected volume rows, divided by the literal physical density, give
jointly measurable reversible-measure densities at every positive time. -/
theorem u1_regular_signed_joint_physical_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ q : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => q z.1 z.2.1 z.2.2) ∧
      (∀ t x y, 0 ≤ q t x y) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ x,
        Integrable (q t x) (physicalReversibleMeasure ω hd lam) ∧
        (∫ y, q t x y ∂physicalReversibleMeasure ω hd lam) = 1 ∧
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          (physicalReversibleMeasure ω hd lam).withDensity
            (fun y => ENNReal.ofReal (q t x y))) ∧
      ∀ (t : ℝ≥0), 0 < t → ∀ y, Continuous (fun x => q t x y) := by
  obtain ⟨p, hp, hn, hrows, hc, _⟩ :=
    u1_regular_signed_kernel_continuous_density_rows hd ω lam Λ hΛ hω
  let ρ := physicalReversibleDensity ω hd lam
  let μ := physicalReversibleMeasure ω hd lam
  let q : ℝ≥0 → Vec d → Vec d → ℝ := fun t x y => p t x y / ρ y
  have hρ : Continuous ρ := physicalReversibleDensity_continuous ω hd lam
  have hρpos (y : Vec d) : 0 < ρ y := physicalReversibleDensity_pos ω hd lam y
  have hq : Measurable (fun z : ℝ≥0 × Vec d × Vec d => q z.1 z.2.1 z.2.2) :=
    hp.div (hρ.measurable.comp measurable_snd.snd)
  have hqn (t : ℝ≥0) (x y : Vec d) : 0 ≤ q t x y :=
    div_nonneg (hn t x y) (hρpos y).le
  have hrep (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        μ.withDensity (fun y => ENNReal.ofReal (q t x y)) := by
    rw [(hrows t ht x).2.2]
    change (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal (p t x y)) =
      (volume.withDensity (fun y => ENNReal.ofReal (ρ y))).withDensity
        (fun y => ENNReal.ofReal (q t x y))
    have hqm : Measurable (q t x) := by
      have hm : Measurable (fun y : Vec d => (t, x, y)) :=
        measurable_const.prodMk (measurable_const.prodMk measurable_id)
      exact hq.comp hm
    rw [← withDensity_mul _ hρ.measurable.ennreal_ofReal hqm.ennreal_ofReal]
    congr 1
    funext y
    change ENNReal.ofReal (p t x y) = ENNReal.ofReal (ρ y) * ENNReal.ofReal (q t x y)
    rw [← ENNReal.ofReal_mul (hρpos y).le]
    congr 1
    dsimp [q]
    field_simp [(hρpos y).ne']
  refine ⟨q, hq, hqn, ?_, ?_⟩
  · intro t ht x
    have hqm : Measurable (q t x) := by
      have hm : Measurable (fun y : Vec d => (t, x, y)) :=
        measurable_const.prodMk (measurable_const.prodMk measurable_id)
      exact hq.comp hm
    have hm : (∫⁻ y, ENNReal.ofReal (q t x y) ∂μ) = 1 := by
      have he := congrArg (fun m : Measure (Vec d) => m Set.univ) (hrep t ht x)
      rw [u2_regular_kernel_conservative] at he
      simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using he.symm
    have hi : Integrable (q t x) μ := by
      have h := integrable_toReal_of_lintegral_ne_top hqm.ennreal_ofReal.aemeasurable (by rw [hm]; simp)
      simpa only [ENNReal.toReal_ofReal (hqn t x _)] using h
    have he := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (hqn t x))
    rw [hm] at he
    have he' := congrArg ENNReal.toReal he
    refine ⟨hi, ?_, hrep t ht x⟩
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (hqn t x)), ENNReal.toReal_one] using he'
  · intro t ht y
    exact (hc t ht y).div_const (ρ y)

#print axioms u1_regular_signed_joint_physical_density

/-- The actual physical density rows are jointly continuous in L¹ at positive times. -/
theorem u1_regular_signed_physical_density_joint_L1
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ q : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => q z.1 z.2.1 z.2.2) ∧
      (∀ t x y, 0 ≤ q t x y) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ x,
        Integrable (q t x) (physicalReversibleMeasure ω hd lam) ∧
        (∫ y, q t x y ∂physicalReversibleMeasure ω hd lam) = 1 ∧
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          (physicalReversibleMeasure ω hd lam).withDensity
            (fun y => ENNReal.ofReal (q t x y))) ∧
      ∀ (t : ℝ≥0), 0 < t → ∀ x,
        Filter.Tendsto (fun z : ℝ≥0 × Vec d =>
          ∫ y, |q z.1 z.2 y - q t x y| ∂physicalReversibleMeasure ω hd lam)
          (𝓝 (t, x)) (𝓝 0) := by
  obtain ⟨p, hp, hn, hrows, hL1⟩ :=
    u1_regular_signed_kernel_joint_L1_row_continuity hd ω lam Λ hΛ hω
  let ρ := physicalReversibleDensity ω hd lam
  let μ := physicalReversibleMeasure ω hd lam
  let q : ℝ≥0 → Vec d → Vec d → ℝ := fun t x y => p t x y / ρ y
  have hρ : Continuous ρ := physicalReversibleDensity_continuous ω hd lam
  have hρpos (y : Vec d) : 0 < ρ y := physicalReversibleDensity_pos ω hd lam y
  have hq : Measurable (fun z : ℝ≥0 × Vec d × Vec d => q z.1 z.2.1 z.2.2) :=
    hp.div (hρ.measurable.comp measurable_snd.snd)
  have hqn (t : ℝ≥0) (x y : Vec d) : 0 ≤ q t x y :=
    div_nonneg (hn t x y) (hρpos y).le
  have hrep (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        μ.withDensity (fun y => ENNReal.ofReal (q t x y)) := by
    rw [(hrows t ht x).2.2]
    change (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal (p t x y)) =
      (volume.withDensity (fun y => ENNReal.ofReal (ρ y))).withDensity
        (fun y => ENNReal.ofReal (q t x y))
    have hqm : Measurable (q t x) := by
      have hm : Measurable (fun y : Vec d => (t, x, y)) :=
        measurable_const.prodMk (measurable_const.prodMk measurable_id)
      exact hq.comp hm
    rw [← withDensity_mul _ hρ.measurable.ennreal_ofReal hqm.ennreal_ofReal]
    congr 1
    funext y
    change ENNReal.ofReal (p t x y) = ENNReal.ofReal (ρ y) * ENNReal.ofReal (q t x y)
    rw [← ENNReal.ofReal_mul (hρpos y).le]
    congr 1
    dsimp [q]
    field_simp [(hρpos y).ne']
  refine ⟨q, hq, hqn, ?_, ?_⟩
  · intro t ht x
    have hqm : Measurable (q t x) := by
      have hm : Measurable (fun y : Vec d => (t, x, y)) :=
        measurable_const.prodMk (measurable_const.prodMk measurable_id)
      exact hq.comp hm
    have hm : (∫⁻ y, ENNReal.ofReal (q t x y) ∂μ) = 1 := by
      have he := congrArg (fun m : Measure (Vec d) => m Set.univ) (hrep t ht x)
      rw [u2_regular_kernel_conservative] at he
      simpa only [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ] using he.symm
    have hi : Integrable (q t x) μ := by
      have h := integrable_toReal_of_lintegral_ne_top hqm.ennreal_ofReal.aemeasurable (by rw [hm]; simp)
      simpa only [ENNReal.toReal_ofReal (hqn t x _)] using h
    have he := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (hqn t x))
    rw [hm] at he
    have he' := congrArg ENNReal.toReal he
    refine ⟨hi, ?_, hrep t ht x⟩
    simpa only [ENNReal.toReal_ofReal (integral_nonneg (hqn t x)), ENNReal.toReal_one] using he'
  · intro t ht x
    apply (hL1 t ht x).congr'
    filter_upwards [] with z
    change (∫ y, |p z.1 z.2 y - p t x y|) =
      ∫ y, |q z.1 z.2 y - q t x y| ∂μ
    change (∫ y, |p z.1 z.2 y - p t x y|) =
      ∫ y, |q z.1 z.2 y - q t x y| ∂(volume.withDensity (fun y => ENNReal.ofReal (ρ y)))
    rw [integral_withDensity_eq_integral_toReal_smul hρ.measurable.ennreal_ofReal
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
    apply integral_congr_ae
    filter_upwards [] with y
    simp only [ENNReal.toReal_ofReal (hρpos y).le, smul_eq_mul, q]
    rw [← sub_div, abs_div, abs_of_pos (hρpos y)]
    field_simp [(hρpos y).ne']

#print axioms u1_regular_signed_physical_density_joint_L1

/-- One physical density representative has both start continuity and joint L¹ row continuity. -/
theorem u1_regular_signed_physical_density_continuous_rows
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ q : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => q z.1 z.2.1 z.2.2) ∧
      (∀ t x y, 0 ≤ q t x y) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ x,
        Integrable (q t x) (physicalReversibleMeasure ω hd lam) ∧
        (∫ y, q t x y ∂physicalReversibleMeasure ω hd lam) = 1 ∧
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          (physicalReversibleMeasure ω hd lam).withDensity
            (fun y => ENNReal.ofReal (q t x y))) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ y, Continuous (fun x => q t x y)) ∧
      ∀ (t : ℝ≥0), 0 < t → ∀ x,
        Filter.Tendsto (fun z : ℝ≥0 × Vec d =>
          ∫ y, |q z.1 z.2 y - q t x y| ∂physicalReversibleMeasure ω hd lam)
          (𝓝 (t, x)) (𝓝 0) := by
  obtain ⟨p, hp, hpn, hpr, hpc⟩ :=
    u1_regular_signed_joint_physical_density hd ω lam Λ hΛ hω
  obtain ⟨q, hq, hqn, hqr, hqL1⟩ :=
    u1_regular_signed_physical_density_joint_L1 hd ω lam Λ hΛ hω
  let μ := physicalReversibleMeasure ω hd lam
  let : SigmaFinite μ := EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω lam
  have hae (t : ℝ≥0) (ht : 0 < t) (x : Vec d) : p t x =ᵐ[μ] q t x := by
    have hp' : Measurable (p t x) := hp.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have hq' : Measurable (q t x) := hq.comp
      (measurable_const.prodMk (measurable_const.prodMk measurable_id))
    have heq : μ.withDensity (fun y => ENNReal.ofReal (p t x y)) =
        μ.withDensity (fun y => ENNReal.ofReal (q t x y)) :=
      (hpr t ht x).2.2.symm.trans (hqr t ht x).2.2
    have h := (withDensity_eq_iff_of_sigmaFinite hp'.ennreal_ofReal.aemeasurable
      hq'.ennreal_ofReal.aemeasurable).mp heq
    filter_upwards [h] with y hy
    simpa only [ENNReal.toReal_ofReal (hpn t x y), ENNReal.toReal_ofReal (hqn t x y)] using
      congrArg ENNReal.toReal hy
  refine ⟨p, hp, hpn, hpr, hpc, ?_⟩
  intro t ht x
  apply (hqL1 t ht x).congr'
  have htime : Tendsto (fun z : ℝ≥0 × Vec d => z.1) (𝓝 (t, x)) (𝓝 t) :=
    continuous_fst.continuousAt
  filter_upwards [htime.eventually (eventually_gt_nhds ht)] with z hz
  apply integral_congr_ae
  filter_upwards [hae z.1 hz z.2, hae t ht x] with y hy hy'
  rw [hy, hy']

#print axioms u1_regular_signed_physical_density_continuous_rows

/-- The selected physical density with continuous start and L¹ rows. -/
noncomputable def u1SelectedPhysicalDensity {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ℝ≥0 → Vec d → Vec d → ℝ :=
  Classical.choose (u1_regular_signed_physical_density_continuous_rows hd ω lam Λ hΛ hω)

/-- Joint positive-time regularity of the selected physical density. -/
def U1SelectedPhysicalDensityJointRegularity {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) : Prop :=
  ContinuousOn (fun z : ℝ≥0 × Vec d × Vec d =>
    u1SelectedPhysicalDensity hd ω lam Λ hΛ hω z.1 z.2.1 z.2.2) {z | 0 < z.1}

/-- Joint regularity of the selected density yields the symmetric physical heat kernel. -/
theorem u1_regular_signed_joint_continuous_symmetric_heat_kernel_of_selected_regularity
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (hjoint : U1SelectedPhysicalDensityJointRegularity hd ω lam Λ hΛ hω) :
    ∃ q : ℝ≥0 → Vec d → Vec d → ℝ,
      Measurable (fun z : ℝ≥0 × Vec d × Vec d => q z.1 z.2.1 z.2.2) ∧
      ContinuousOn (fun z : ℝ≥0 × Vec d × Vec d => q z.1 z.2.1 z.2.2)
        {z | 0 < z.1} ∧
      (∀ t x y, 0 ≤ q t x y) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ x,
        Integrable (q t x) (physicalReversibleMeasure ω hd lam) ∧
        (∫ y, q t x y ∂physicalReversibleMeasure ω hd lam) = 1 ∧
        u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
          (physicalReversibleMeasure ω hd lam).withDensity
            (fun y => ENNReal.ofReal (q t x y))) ∧
      (∀ (t : ℝ≥0), 0 < t → ∀ x y, q t x y = q t y x) := by
  let q := u1SelectedPhysicalDensity hd ω lam Λ hΛ hω
  have hq := Classical.choose_spec
    (u1_regular_signed_physical_density_continuous_rows hd ω lam Λ hΛ hω)
  change Measurable (fun z : ℝ≥0 × Vec d × Vec d => q z.1 z.2.1 z.2.2) ∧
    (∀ t x y, 0 ≤ q t x y) ∧
    (∀ (t : ℝ≥0), 0 < t → ∀ x,
      Integrable (q t x) (physicalReversibleMeasure ω hd lam) ∧
      (∫ y, q t x y ∂physicalReversibleMeasure ω hd lam) = 1 ∧
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        (physicalReversibleMeasure ω hd lam).withDensity
          (fun y => ENNReal.ofReal (q t x y))) ∧ _ at hq
  refine ⟨q, hq.1, hjoint, hq.2.1, hq.2.2.1, ?_⟩
  intro t ht
  have hopen : IsOpen {z : ℝ≥0 × Vec d × Vec d | 0 < z.1} :=
    isOpen_lt continuous_const continuous_fst
  have hc : Continuous (Function.uncurry (q t)) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    have h := hjoint.continuousAt (hopen.mem_nhds (show 0 < (t, z.1, z.2).1 from ht))
    exact h.comp (continuous_const.prodMk continuous_id).continuousAt
  exact u1_regular_continuous_reversible_density_symmetric hd ω lam Λ hΛ hω t
    (q t) hc (hq.2.1 t) (fun x => (hq.2.2.1 t ht x).2.2)

#print axioms u1_regular_signed_joint_continuous_symmetric_heat_kernel_of_selected_regularity

/-- The supplied path law restarts from its actual endpoint on every
measurable deterministic-past event. -/
theorem u1_supplied_deterministic_restrict_shift
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (s : ℝ≥0) (x : Vec d) (A : Set (Path d))
    (hA : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] A) :
    ((r.pathLaw x).restrict A).map (MarkovProcess.ContinuousPath.shift s) =
      Kernel.comap r.pathLaw (MarkovProcess.ContinuousPath.coordinateProcess s)
        (MarkovProcess.ContinuousPath.measurable_coordinateProcess s) ∘ₘ
          ((r.pathLaw x).restrict A) := by
  letI : IsMarkovKernel r.pathLaw := r.pathLaw_isMarkovKernel
  exact (u2RegularC0KernelSemigroup_isFeller hd ω lam Λ hΛ hω).realization_restrict_map_shift
    (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω)
    (u2_regular_kernel_conservative hd ω lam Λ hΛ hω)
    ⟨fun _ => 0, continuous_const⟩ r.pathLaw
    (u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam Λ hΛ hω h0 h1 r) x s A hA

#print axioms u1_supplied_deterministic_restrict_shift

/-- Deterministic past and future factor through the actual supplied path law. -/
theorem u1_supplied_deterministic_past_future_factorization
    {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ) (hΛ : 1 ≤ Λ) (ω : FieldPair d)
    (hω : IsRegular Λ ω) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (s : ℝ≥0) (x : Vec d)
    (H : (ℝ≥0 → Vec d) → ℝ≥0∞) (hH : Measurable H)
    (F : Path d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ γ : Path d,
      H (fun t : ℝ≥0 => γ (min t s)) *
        F (MarkovProcess.ContinuousPath.shift s γ) ∂r.pathLaw x) =
    ∫⁻ γ : Path d,
      H (fun t : ℝ≥0 => γ (min t s)) *
        (∫⁻ η : Path d, F η ∂r.pathLaw (γ s)) ∂r.pathLaw x := by
  letI : IsMarkovKernel r.pathLaw := r.pathLaw_isMarkovKernel
  have hW : Measurable[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] (fun γ : Path d => H (fun t : ℝ≥0 => γ (min t s))) := by
    letI : MeasurableSpace (Path d) :=
      MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s
    apply hH.comp
    apply measurable_pi_iff.mpr
    intro t
    exact (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
      (min t s)).mono ((MarkovProcess.ContinuousPath.canonicalFiltration
        (alpha := Vec d)).mono (min_le_right t s)) le_rfl
  have h := MarkovProcess.StoppingTime.lintegral_mul_indicator_of_restrict_map
    (r.pathLaw x)
    (Kernel.comap r.pathLaw (MarkovProcess.ContinuousPath.coordinateProcess s)
      (MarkovProcess.ContinuousPath.measurable_coordinateProcess s))
    (MarkovProcess.ContinuousPath.shift s)
    (MarkovProcess.ContinuousPath.measurable_shift_fixed s)
    ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le s)
    Set.univ MeasurableSet.univ
    (fun A hA => by
      simpa only [Set.inter_univ] using
        u1_supplied_deterministic_restrict_shift hd Λ hΛ ω hω lam h0 h1 r s x A hA)
    F hF (fun γ => H (fun t => γ (min t s))) hW
  simpa only [Set.indicator_univ, Kernel.comap_apply,
    MarkovProcess.ContinuousPath.coordinateProcess_apply] using h

#print axioms u1_supplied_deterministic_past_future_factorization


/-- The supplied transition at a positive time and fixed start has a bounded density. -/
theorem u1_supplied_transition_has_bounded_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    ∃ p : Vec d → ℝ, Measurable p ∧ (∀ y, 0 ≤ p y) ∧
      Integrable p volume ∧ (∫ y, p y ∂volume) = 1 ∧
      r.transitionKernel t x = volume.withDensity (fun y => ENNReal.ofReal (p y)) ∧
      ∃ C : ℝ, ∀ y, p y ≤ C := by
  obtain ⟨M, p, hM, hp, hb, hi, hr⟩ :=
    u1_supplied_gmp_transition_bounded_normalized_density hd ω lam Λ hΛ hω h0 h1 r t ht
  exact ⟨p x, hp.comp (measurable_const.prodMk measurable_id),
    fun y => (hb x y).1, (hi x).1, (hi x).2, hr x, M, fun y => (hb x y).2⟩

#print axioms u1_supplied_transition_has_bounded_density

/-- A path kernel with the regular signed semigroup finite-dimensional laws
factors deterministic past and future through its actual endpoint. -/
theorem u1_canonical_signed_path_deterministic_factorization
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (omega : FieldPair d)
    (homega : IsRegular L omega) (lam : ℝ)
    (K : Kernel (Vec d) (Path d)) [IsMarkovKernel K]
    (hFDD : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel (u2RegularC0KernelSemigroup hd omega lam L hL homega) I)
    (s : ℝ≥0) (x : Vec d)
    (H : (ℝ≥0 → Vec d) → ℝ≥0∞) (hH : Measurable H)
    (F : Path d → ℝ≥0∞) (hF : Measurable F) :
    (∫⁻ gamma : Path d, H (fun t => gamma (min t s)) *
      F (MarkovProcess.ContinuousPath.shift s gamma) ∂K x) =
    ∫⁻ gamma : Path d, H (fun t => gamma (min t s)) *
      (∫⁻ eta : Path d, F eta ∂K (gamma s)) ∂K x := by
  have hW : Measurable[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] (fun γ : Path d => H (fun t : ℝ≥0 => γ (min t s))) := by
    let : MeasurableSpace (Path d) :=
      MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s
    apply hH.comp
    apply measurable_pi_iff.mpr
    intro t
    exact (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
      (min t s)).mono ((MarkovProcess.ContinuousPath.canonicalFiltration
        (alpha := Vec d)).mono (min_le_right t s)) le_rfl
  have h := MarkovProcess.StoppingTime.lintegral_mul_indicator_of_restrict_map
    (K x)
    (Kernel.comap K (MarkovProcess.ContinuousPath.coordinateProcess s)
      (MarkovProcess.ContinuousPath.measurable_coordinateProcess s))
    (MarkovProcess.ContinuousPath.shift s)
    (MarkovProcess.ContinuousPath.measurable_shift_fixed s)
    ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le s)
    Set.univ MeasurableSet.univ
    (fun A hA => by
      simpa only [Set.inter_univ] using
        (u2RegularC0KernelSemigroup_isFeller hd omega lam L hL homega).realization_restrict_map_shift
          (u2RegularC0KernelSemigroup hd omega lam L hL homega)
          (u2_regular_kernel_conservative hd omega lam L hL homega)
          ⟨fun _ => 0, continuous_const⟩ K hFDD x s A hA)
    F hF (fun γ => H (fun t => γ (min t s))) hW
  simpa only [Set.indicator_univ, Kernel.comap_apply,
    MarkovProcess.ContinuousPath.coordinateProcess_apply] using h

#print axioms u1_canonical_signed_path_deterministic_factorization

/-- The canonical finite-dimensional distributions give the bounded real
past/future identity for any real force. -/
theorem u1_canonical_signed_path_real_factorization
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (K : Kernel (Vec d) (Path d))
    [IsMarkovKernel K]
    (hFDD : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam L hL hω) I)
    (s : ℝ≥0) (x : Vec d)
    (H : (ℝ≥0 → Vec d) → ℝ) (hH : Measurable H)
    (MH : ℝ) (hHbound : ∀ p, |H p| ≤ MH)
    (F : Path d → ℝ) (hF : Measurable F)
    (MF : ℝ) (hFbound : ∀ γ, |F γ| ≤ MF) :
    (∫ γ : Path d, H (fun t : ℝ≥0 => γ (min t s)) *
      F (MarkovProcess.ContinuousPath.shift s γ) ∂K x) =
    ∫ γ : Path d, H (fun t : ℝ≥0 => γ (min t s)) *
      (∫ η : Path d, F η ∂K (γ s)) ∂K x := by
  have hMH (p) : ‖H p‖ ≤ MH := by simpa only [Real.norm_eq_abs] using hHbound p
  have hMF (p) : ‖F p‖ ≤ MF := by simpa only [Real.norm_eq_abs] using hFbound p
  let W : Path d → ℝ := fun γ => H (fun t : ℝ≥0 => γ (min t s))
  have hWm : Measurable[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] W := by
    let : MeasurableSpace (Path d) :=
      MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s
    apply hH.comp
    apply measurable_pi_iff.mpr
    intro t
    exact (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
      (min t s)).mono ((MarkovProcess.ContinuousPath.canonicalFiltration
        (alpha := Vec d)).mono (min_le_right t s)) le_rfl
  have hW : StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] W := hWm.stronglyMeasurable
  have hrestart (A : Set (Path d))
      (hA : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
        (alpha := Vec d) s] A) :
      ((K x).restrict A).map (MarkovProcess.ContinuousPath.shift s) =
        Kernel.comap K (MarkovProcess.ContinuousPath.coordinateProcess s)
          (MarkovProcess.ContinuousPath.measurable_coordinateProcess s) ∘ₘ
            ((K x).restrict A) := by
    exact (u2RegularC0KernelSemigroup_isFeller hd ω lam L hL hω).realization_restrict_map_shift
      (u2RegularC0KernelSemigroup hd ω lam L hL hω)
      (u2_regular_kernel_conservative hd ω lam L hL hω)
      ⟨fun _ => 0, continuous_const⟩ K hFDD x s A hA
  have hIntF : Integrable (fun γ => F (MarkovProcess.ContinuousPath.shift s γ)) (K x) :=
    Integrable.of_bound (hF.comp (MarkovProcess.ContinuousPath.measurable_shift_fixed s)).aestronglyMeasurable
      MF (Filter.Eventually.of_forall fun γ => hMF _)
  have hIntWF : Integrable (fun γ => W γ * F (MarkovProcess.ContinuousPath.shift s γ)) (K x) := by
    apply Integrable.of_bound
      ((hWm.mono ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le s) le_rfl).mul
        (hF.comp (MarkovProcess.ContinuousPath.measurable_shift_fixed s))).aestronglyMeasurable
      (|MH| * |MF|)
    apply Filter.Eventually.of_forall
    intro γ
    change ‖W γ * F (MarkovProcess.ContinuousPath.shift s γ)‖ ≤ |MH| * |MF|
    rw [norm_mul]
    exact mul_le_mul (le_trans (hMH _) (le_abs_self MH))
      (le_trans (hMF _) (le_abs_self MF)) (norm_nonneg _) (abs_nonneg _)
  have hcond := MarkovProcess.ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
    K x s hrestart F hF.stronglyMeasurable MF hMF
  have hpull := condExp_mul_of_stronglyMeasurable_left (μ := K x) hW hIntWF hIntF
  calc
    _ = ∫ γ, (K x)[fun η => W η * F (MarkovProcess.ContinuousPath.shift s η) |
        MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s] γ ∂K x :=
      (integral_condExp ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le s)).symm
    _ = ∫ γ, W γ * ((K x)[fun η => F (MarkovProcess.ContinuousPath.shift s η) |
        MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s] γ) ∂K x :=
      integral_congr_ae hpull
    _ = _ := integral_congr_ae (hcond.mono fun γ hγ => by
      change W γ * _ = W γ * _
      rw [hγ])


#print axioms u1_canonical_signed_path_real_factorization

/-- The canonical finite-dimensional distributions give the bounded complex
past/future identity for any real force. -/
theorem u1_canonical_signed_path_complex_factorization
    {d : ℕ} (hd : 2 ≤ d) (L : ℝ) (hL : 1 ≤ L) (ω : FieldPair d)
    (hω : IsRegular L ω) (lam : ℝ) (K : Kernel (Vec d) (Path d))
    [IsMarkovKernel K]
    (hFDD : ∀ I : Finset ℝ≥0,
      K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam L hL hω) I)
    (s : ℝ≥0) (x : Vec d)
    (H : (ℝ≥0 → Vec d) → ℂ) (hH : Measurable H)
    (MH : ℝ) (hHbound : ∀ p, ‖H p‖ ≤ MH)
    (F : Path d → ℂ) (hF : Measurable F)
    (MF : ℝ) (hFbound : ∀ γ, ‖F γ‖ ≤ MF) :
    (∫ γ : Path d, H (fun t : ℝ≥0 => γ (min t s)) *
      F (MarkovProcess.ContinuousPath.shift s γ) ∂K x) =
    ∫ γ : Path d, H (fun t : ℝ≥0 => γ (min t s)) *
      (∫ η : Path d, F η ∂K (γ s)) ∂K x := by
  let W : Path d → ℂ := fun γ => H (fun t : ℝ≥0 => γ (min t s))
  have hWm : Measurable[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] W := by
    let : MeasurableSpace (Path d) :=
      MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s
    apply hH.comp
    apply measurable_pi_iff.mpr
    intro t
    exact (MarkovProcess.ContinuousPath.measurable_coordinateProcess_canonicalFiltration
      (min t s)).mono ((MarkovProcess.ContinuousPath.canonicalFiltration
        (alpha := Vec d)).mono (min_le_right t s)) le_rfl
  have hW : StronglyMeasurable[MarkovProcess.ContinuousPath.canonicalFiltration
      (alpha := Vec d) s] W := hWm.stronglyMeasurable
  have hcomap : MeasurableSpace.comap
      (fun γ : Path d => fun t : ℝ≥0 => γ (min t s)) inferInstance =
      MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s := by
    change MeasurableSpace.comap (fun γ : Path d => fun t : ℝ≥0 => γ (min t s))
      (⨆ t : ℝ≥0, MeasurableSpace.comap (fun f : ℝ≥0 → Vec d => f t) inferInstance) = _
    rw [MeasurableSpace.comap_iSup]
    simp only [MeasurableSpace.comap_comp]
    apply le_antisymm
    · apply iSup_le
      intro t
      change MeasurableSpace.comap (MarkovProcess.ContinuousPath.coordinateProcess (min t s))
        inferInstance ≤ _
      exact le_iSup_of_le (⟨min t s, min_le_right t s⟩ : Set.Iic s) le_rfl
    · change (⨆ t : Set.Iic s, MeasurableSpace.comap
          (MarkovProcess.ContinuousPath.coordinateProcess (t : ℝ≥0)) inferInstance) ≤ _
      apply iSup_le
      intro t
      have h := le_iSup (fun u : ℝ≥0 => MeasurableSpace.comap
        (fun γ : Path d => γ (min u s)) inferInstance) (t : ℝ≥0)
      have ht : (t : ℝ≥0) ≤ s := t.property
      change MeasurableSpace.comap (fun γ : Path d => γ (t : ℝ≥0)) inferInstance ≤ _
      simpa only [min_eq_left ht, Function.comp_def] using h
  have hrestart (A : Set (Path d))
      (hA : MeasurableSet[MarkovProcess.ContinuousPath.canonicalFiltration
        (alpha := Vec d) s] A) :
      ((K x).restrict A).map (MarkovProcess.ContinuousPath.shift s) =
        Kernel.comap K (MarkovProcess.ContinuousPath.coordinateProcess s)
          (MarkovProcess.ContinuousPath.measurable_coordinateProcess s) ∘ₘ
            ((K x).restrict A) := by
    classical
    have hAfull : MeasurableSet A :=
      ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le s) A hA
    obtain ⟨B, hB, hpre⟩ : ∃ B : Set (ℝ≥0 → Vec d), MeasurableSet B ∧
        (fun γ : Path d => fun t : ℝ≥0 => γ (min t s)) ⁻¹' B = A := by
      apply MeasurableSpace.measurableSet_comap.mp
      rwa [hcomap]
    have hind (γ : Path d) :
        B.indicator (fun _ => (1 : ℝ≥0∞)) (fun t => γ (min t s)) =
          A.indicator (fun _ => (1 : ℝ≥0∞)) γ := by
      have hm : (fun t => γ (min t s)) ∈ B ↔ γ ∈ A := by
        change γ ∈ (fun γ : Path d => fun t => γ (min t s)) ⁻¹' B ↔ _
        rw [hpre]
      simp only [Set.indicator_apply, hm]
    ext C hC
    have h := u1_canonical_signed_path_deterministic_factorization hd L hL ω hω lam K hFDD s x
      (B.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hB)
      (C.indicator (fun _ => (1 : ℝ≥0∞))) (measurable_const.indicator hC)
    simp only [hind] at h
    have hCint (y : Vec d) :
        (∫⁻ η, C.indicator (fun _ => (1 : ℝ≥0∞)) η ∂K y) = K y C :=
      lintegral_indicator_one hC
    simp_rw [hCint] at h
    rw [Measure.map_apply (MarkovProcess.ContinuousPath.measurable_shift_fixed s) hC,
      Measure.restrict_apply ((MarkovProcess.ContinuousPath.measurable_shift_fixed s) hC),
      Measure.bind_apply hC (Kernel.aemeasurable _)]
    simp only [Kernel.comap_apply, MarkovProcess.ContinuousPath.coordinateProcess_apply]
    rw [← lintegral_indicator_one
      (((MarkovProcess.ContinuousPath.measurable_shift_fixed s) hC).inter hAfull),
      ← lintegral_indicator hAfull]
    convert h using 1 <;> apply lintegral_congr <;> intro γ <;>
      by_cases ha : γ ∈ A <;>
      by_cases hc : MarkovProcess.ContinuousPath.shift s γ ∈ C <;>
      simp [Set.indicator_apply, ha, hc, Set.mem_inter_iff]
  have hIntF : Integrable (fun γ => F (MarkovProcess.ContinuousPath.shift s γ)) (K x) :=
    Integrable.of_bound (hF.comp (MarkovProcess.ContinuousPath.measurable_shift_fixed s)).aestronglyMeasurable
      MF (Filter.Eventually.of_forall fun γ => hFbound _)
  have hIntWF : Integrable (fun γ => W γ * F (MarkovProcess.ContinuousPath.shift s γ)) (K x) := by
    apply Integrable.of_bound
      ((hWm.mono ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le s) le_rfl).mul
        (hF.comp (MarkovProcess.ContinuousPath.measurable_shift_fixed s))).aestronglyMeasurable
      (|MH| * |MF|)
    apply Filter.Eventually.of_forall
    intro γ
    change ‖W γ * F (MarkovProcess.ContinuousPath.shift s γ)‖ ≤ |MH| * |MF|
    rw [norm_mul]
    exact mul_le_mul (le_trans (hHbound _) (le_abs_self MH))
      (le_trans (hFbound _) (le_abs_self MF)) (norm_nonneg _) (abs_nonneg _)
  have hcond := MarkovProcess.ContinuousPath.condExp_shift_ae_eq_integral_pathKernel_of_restrict_map
    K x s hrestart F hF.stronglyMeasurable MF hFbound
  have hpull := condExp_bilin_of_stronglyMeasurable_left (μ := K x)
    (ContinuousLinearMap.mul ℝ ℂ) hW hIntWF hIntF
  calc
    _ = ∫ γ, (K x)[fun η => W η * F (MarkovProcess.ContinuousPath.shift s η) |
        MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s] γ ∂K x :=
      (integral_condExp ((MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)).le s)).symm
    _ = ∫ γ, W γ * ((K x)[fun η => F (MarkovProcess.ContinuousPath.shift s η) |
        MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d) s] γ) ∂K x :=
      integral_congr_ae hpull
    _ = _ := integral_congr_ae (hcond.mono fun γ hγ => by
      change W γ * _ = W γ * _
      rw [hγ])


#print axioms u1_canonical_signed_path_complex_factorization

/-- Every supplied regular GMP realization restarts at finite extended stopping times. -/
theorem u1_supplied_regular_extended_stopping_restart
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (G : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1)
    (T : Path d → WithTop ℝ≥0)
    (hT : IsStoppingTime (MarkovProcess.ContinuousPath.canonicalFiltration (alpha := Vec d)) T)
    (x : Vec d) :
    ∀ A : Set (Path d), MeasurableSet[hT.measurableSpace] A →
      (∀ γ ∈ A, T γ < ⊤) →
      ((G.pathLaw x).restrict A).map
        (fun γ => MarkovProcess.ContinuousPath.shift ((T γ).untopD 0) γ) =
      Measure.bind ((G.pathLaw x).restrict A) (fun γ => G.pathLaw (γ ((T γ).untopD 0))) := by
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  exact u1_regular_signed_extended_stopping_restart hd ω lam Λ hΛ hω G.pathLaw
    (u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam Λ hΛ hω h0 h1 G) T hT x


end EinsteinFull
