import EinsteinFull.Calculus.C20TubeWeightedTimeAverageLimit
import EinsteinFull.Calculus.C18TubeWeightedTimeMollification
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open EinsteinRelation MeasureTheory Filter
open scoped Topology NNReal ENNReal

namespace EinsteinFull.Calculus

/-- A bounded second derivative gives a global linear bound on the first derivative. -/
theorem c20_deriv_linear_growth (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (M : ℝ) (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) (x : ℝ) :
    |deriv F x| ≤ |deriv F 0| + M * |x| := by
  have h := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.univ) (f := deriv F) (C := M)
    (fun t _ => hF.differentiable_deriv_two t)
    (fun t _ => by simpa only [Real.norm_eq_abs] using hF2 t)
    convex_univ (Set.mem_univ (0 : ℝ)) (Set.mem_univ x)
  have h' : |deriv F x - deriv F 0| ≤ M * |x| := by
    simpa only [Real.norm_eq_abs, sub_zero] using h
  have ht := abs_add_le (deriv F x - deriv F 0) (deriv F 0)
  have he : deriv F x - deriv F 0 + deriv F 0 = deriv F x := by ring
  rw [he] at ht
  linarith

/-- A bounded second derivative controls increments by a quadratic-growth factor. -/
theorem c20_nonlinear_increment_bound (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F)
    (M : ℝ) (hM : 0 ≤ M) (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (x y : ℝ) :
    |F y - F x| ≤ (|deriv F 0| + M * (|x| + |y|)) * |y - x| := by
  let C := |deriv F 0| + M * (|x| + |y|)
  have hb : ∀ t ∈ Set.Icc (min x y) (max x y), ‖deriv F t‖ ≤ C := by
    intro t ht
    have ht' : |t| ≤ |x| + |y| := by
      have h := abs_le_max_abs_abs ht.1 ht.2
      have hmin : |min x y| ≤ |x| + |y| := by
        rcases le_total x y with hxy | hyx
        · rw [min_eq_left hxy]; linarith [abs_nonneg y]
        · rw [min_eq_right hyx]; linarith [abs_nonneg x]
      have hmax : |max x y| ≤ |x| + |y| := by
        rcases le_total x y with hxy | hyx
        · rw [max_eq_right hxy]; linarith [abs_nonneg x]
        · rw [max_eq_left hyx]; linarith [abs_nonneg y]
      exact h.trans (max_le hmin hmax)
    rw [Real.norm_eq_abs]
    calc
      |deriv F t| ≤ |deriv F 0| + M * |t| := c20_deriv_linear_growth F hF M hF2 t
      _ ≤ C := by dsimp [C]; gcongr
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := Set.Icc (min x y) (max x y)) (f := F) (C := C)
    (fun t _ => hF.differentiable (by norm_num) t) hb (convex_Icc _ _)
    ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
  simpa only [Real.norm_eq_abs] using hh

/-- Bounded continuous multipliers converging in measure may be integrated against
an arbitrary fixed integrable function. -/
theorem c20_integral_bounded_comp_tendsto_in_measure
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    [l.IsCountablyGenerated] (f : ι → Ω → ℝ) (u : Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfu : TendstoInMeasure μ f l u)
    (φ : ℝ → ℝ) (hφ : Continuous φ) (M : ℝ)
    (hφb : ∀ x, |φ x| ≤ M) (g : Ω → ℝ) (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, φ (f n x) * g x ∂μ) l
      (𝓝 (∫ x, φ (u x) * g x ∂μ)) := by
  refine tendsto_of_subseq_tendsto fun ns hns => ?_
  obtain ⟨ms, _, hpoint⟩ := (hfu.comp hns).exists_seq_tendsto_ae
  refine ⟨ms, ?_⟩
  apply tendsto_integral_of_dominated_convergence (fun x => M * |g x|)
  · intro n
    exact (hφ.comp_aestronglyMeasurable (hf (ns (ms n)))).mul hg.aestronglyMeasurable
  · exact hg.abs.const_mul M
  · intro n
    filter_upwards with x
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (hφb _) (abs_nonneg _)
  · filter_upwards [hpoint] with x hx
    exact (hφ.continuousAt.tendsto.comp hx).mul tendsto_const_nhds

/-- The bounded second derivative passes to the limit against fixed integrable energy. -/
theorem c20_integral_second_deriv_tendsto_in_measure
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    [l.IsCountablyGenerated] (f : ι → Ω → ℝ) (u : Ω → ℝ)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ)
    (hfu : TendstoInMeasure μ f l u)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) (g : Ω → ℝ) (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, deriv (deriv F) (f n x) * g x ∂μ) l
      (𝓝 (∫ x, deriv (deriv F) (u x) * g x ∂μ)) := by
  have hF' : ContDiff ℝ 1 (deriv F) := hF.deriv'
  exact c20_integral_bounded_comp_tendsto_in_measure f u hf hfu
    (deriv (deriv F)) hF'.continuous_deriv_one M hF2 g hg

/-- Convergence of the scalar squared error implies convergence in measure. -/
theorem c20_tendsto_in_measure_of_integral_sq
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    (f : ι → Ω → ℝ) (u : Ω → ℝ)
    (hmem : ∀ᶠ n in l, MemLp (f n - u) 2 μ)
    (hlim : Tendsto (fun n => ∫ x, |f n x - u x| ^ 2 ∂μ) l (𝓝 0)) :
    TendstoInMeasure μ f l u := by
  apply tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  have hsqrt : Tendsto (fun n => ENNReal.ofReal (Real.sqrt (∫ x, |f n x - u x| ^ 2 ∂μ)))
      l (𝓝 0) := by
    have ht := ENNReal.continuous_ofReal.continuousAt.tendsto.comp
      (Real.continuous_sqrt.continuousAt.tendsto.comp hlim)
    simpa only [Function.comp_def, Real.sqrt_zero, ENNReal.ofReal_zero] using ht
  apply hsqrt.congr'
  filter_upwards [hmem] with n hn
  rw [hn.eLpNorm_eq_integral_rpow_norm (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat, Pi.sub_apply, Real.norm_eq_abs,
    Real.sqrt_eq_rpow]
  norm_num

/-- The literal forward-average error has L² regularity on the smaller slab. -/
theorem c20_scalar_forward_average_slab_memLp {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U)))
    {h : ℝ} (hh : 0 ≤ h) (hhsmall : h ≤ 1 / 2) :
    MemLp (fun z => h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) - u z) 2
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) := by
  let S := Set.Ioo (-1 : ℝ) 1 ×ˢ U
  let T := Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U
  have hS : MeasurableSet S := measurableSet_Ioo.prod hU
  have hT : MeasurableSet T := measurableSet_Ioo.prod hU
  let v := S.indicator u
  have hv : MemLp v 2 (volume : Measure (ℝ × Vec d)) :=
    (memLp_indicator_iff_restrict hS).2 hu
  let F := hv.aestronglyMeasurable.mk v
  have hF : Measurable F := hv.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hvF : v =ᵐ[volume] F := hv.aestronglyMeasurable.ae_eq_mk
  let f := hv.toLp v
  have hFf : F =ᵐ[volume] f := hvF.symm.trans hv.coeFn_toLp.symm
  let q : Lp ℝ 2 (volume : Measure (ℝ × Vec d)) :=
    h⁻¹ • ∫ s in (0 : ℝ)..h, Lp.compMeasurePreserving (c20TimeTranslate s)
      (c20_time_translate_measurePreserving s) f
  have havg := c20_time_translate_integral_ae f F hF hFf hh
  have hsmul := Lp.coeFn_smul h⁻¹ (∫ s in (0 : ℝ)..h,
    Lp.compMeasurePreserving (c20TimeTranslate s)
      (c20_time_translate_measurePreserving s) f)
  have hsub := Lp.coeFn_sub q f
  have he : (fun z => (q - f) z) =ᵐ[volume.restrict T]
      (fun z => h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) - u z) := by
    filter_upwards [ae_restrict_of_ae havg, ae_restrict_of_ae hsmul,
      ae_restrict_of_ae hsub, ae_restrict_of_ae hFf,
      ae_restrict_of_ae hvF, ae_restrict_of_ae (c20_forward_integral_ae_congr v F hvF h),
      ae_restrict_mem hT] with z ha hs hd hr hvz hi hz
    have hzS : z ∈ S := ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
    have huval : v z = u z := Set.indicator_of_mem hzS _
    have huavg := c20_forward_integral_indicator_slab U u z h hz hh hhsmall
    change q z = h⁻¹ * (∫ s in (0 : ℝ)..h,
      Lp.compMeasurePreserving (c20TimeTranslate s)
        (c20_time_translate_measurePreserving s) f) z at hs
    rw [ha] at hs
    change (q - f) z = q z - f z at hd
    change (∫ s in (0 : ℝ)..h, v (z.1 + s, z.2)) = _ at huavg
    rw [hd, hs, ← hr, ← hvz, huval, ← hi, huavg]
  exact (memLp_congr_ae he).mp
    (MemLp.mono_measure (ν := volume.restrict T) Measure.restrict_le_self (Lp.memLp (q - f)))

/-- Scalar forward averages on the smaller slab converge in measure. -/
theorem c20_scalar_forward_average_slab_tendsto_in_measure {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    TendstoInMeasure (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U))
      (fun h z => h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) (𝓝[>] 0) u := by
  apply c20_tendsto_in_measure_of_integral_sq
  · have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 / 2 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhsmall
    exact c20_scalar_forward_average_slab_memLp U hU u hu (le_of_lt hh) (le_of_lt hhsmall)
  · exact c20_scalar_forward_average_slab_L2 U hU u hu

/-- Eventual measurability suffices for bounded multiplier convergence. -/
theorem c20_integral_bounded_comp_tendsto_in_measure_eventually
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    [l.IsCountablyGenerated] (f : ι → Ω → ℝ) (u : Ω → ℝ)
    (hf : ∀ᶠ n in l, AEStronglyMeasurable (f n) μ)
    (hfu : TendstoInMeasure μ f l u)
    (φ : ℝ → ℝ) (hφ : Continuous φ) (M : ℝ)
    (hφb : ∀ x, |φ x| ≤ M) (g : Ω → ℝ) (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, φ (f n x) * g x ∂μ) l
      (𝓝 (∫ x, φ (u x) * g x ∂μ)) := by
  classical
  let f' : ι → Ω → ℝ := fun n =>
    if AEStronglyMeasurable (f n) μ then f n else 0
  have hf' : ∀ n, AEStronglyMeasurable (f' n) μ := by
    intro n
    by_cases hn : AEStronglyMeasurable (f n) μ
    · simpa [f', hn] using hn
    · simpa [f', hn] using
        (aestronglyMeasurable_zero : AEStronglyMeasurable (0 : Ω → ℝ) μ)
  have he : ∀ᶠ n in l, f n = f' n := by
    filter_upwards [hf] with n hn
    simp [f', hn]
  have hfu' : TendstoInMeasure μ f' l u :=
    hfu.congr' (he.mono fun _ hn => Filter.Eventually.of_forall fun x => congrFun hn x)
      Filter.EventuallyEq.rfl
  have hl := c20_integral_bounded_comp_tendsto_in_measure f' u hf' hfu' φ hφ M hφb g hg
  apply hl.congr'
  filter_upwards [he] with n hn
  rw [hn]

/-- A bounded continuous composition converging in measure converges in weighted L¹. -/
theorem c20_integral_abs_bounded_comp_tendsto_in_measure
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    [l.IsCountablyGenerated] (f : ι → Ω → ℝ) (u : Ω → ℝ)
    (hf : ∀ᶠ n in l, AEStronglyMeasurable (f n) μ)
    (hu : AEStronglyMeasurable u μ) (hfu : TendstoInMeasure μ f l u)
    (φ : ℝ → ℝ) (hφ : Continuous φ) (M : ℝ)
    (hφb : ∀ x, |φ x| ≤ M) (g : Ω → ℝ) (hg : Integrable g μ) :
    Tendsto (fun n => ∫ x, |φ (f n x) - φ (u x)| * |g x| ∂μ) l (𝓝 0) := by
  classical
  let f' : ι → Ω → ℝ := fun n => if AEStronglyMeasurable (f n) μ then f n else 0
  have hf' : ∀ n, AEStronglyMeasurable (f' n) μ := by
    intro n
    by_cases hn : AEStronglyMeasurable (f n) μ
    · simpa [f', hn] using hn
    · simpa [f', hn] using
        (aestronglyMeasurable_zero : AEStronglyMeasurable (0 : Ω → ℝ) μ)
  have he : ∀ᶠ n in l, f n = f' n := by
    filter_upwards [hf] with n hn
    simp [f', hn]
  have hfu' : TendstoInMeasure μ f' l u :=
    hfu.congr' (he.mono fun _ hn => Filter.Eventually.of_forall fun x => congrFun hn x)
      Filter.EventuallyEq.rfl
  have ht : Tendsto (fun n => ∫ x, |φ (f' n x) - φ (u x)| * |g x| ∂μ) l (𝓝 0) := by
    refine tendsto_of_subseq_tendsto fun ns hns => ?_
    obtain ⟨ms, _, hpoint⟩ := (hfu'.comp hns).exists_seq_tendsto_ae
    refine ⟨ms, ?_⟩
    have hc : Tendsto (fun n : ℕ => ∫ x, |φ (f' (ns (ms n)) x) - φ (u x)| * |g x| ∂μ)
        atTop (𝓝 (∫ _x, (0 : ℝ) ∂μ)) := by
      apply tendsto_integral_of_dominated_convergence (fun x => (2 * M) * |g x|)
      · intro n
        have hm := (hφ.comp_aestronglyMeasurable (hf' (ns (ms n)))).sub
          (hφ.comp_aestronglyMeasurable hu)
        exact (continuous_abs.comp_aestronglyMeasurable hm).mul hg.abs.aestronglyMeasurable
      · exact hg.abs.const_mul (2 * M)
      · intro n
        filter_upwards with x
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))]
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        calc
          |φ (f' (ns (ms n)) x) - φ (u x)| ≤ |φ (f' (ns (ms n)) x)| + |φ (u x)| := abs_sub _ _
          _ ≤ 2 * M := by linarith [hφb (f' (ns (ms n)) x), hφb (u x)]
      · filter_upwards [hpoint] with x hx
        have hh := ((hφ.continuousAt.tendsto.comp hx).sub
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => φ (u x)) atTop (𝓝 (φ (u x))))).abs.mul
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => |g x|) atTop (𝓝 |g x|))
        simpa using hh
    simpa using hc
  apply ht.congr'
  filter_upwards [he] with n hn
  rw [hn]

/-- The scalar forward average has the required measurability for small steps. -/
theorem c20_scalar_forward_average_slab_eventually_aestronglyMeasurable {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    ∀ᶠ h : ℝ in 𝓝[>] 0, AEStronglyMeasurable
      (fun z => h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)))
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) := by
  have hus : MemLp u 2 (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) := by
    apply MemLp.mono_measure (Measure.restrict_mono_set volume ?_) hu
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhsmall
  have he := c20_scalar_forward_average_slab_memLp U hU u hu (le_of_lt hh) (le_of_lt hhsmall)
  have ha := he.aestronglyMeasurable.add hus.aestronglyMeasurable
  convert ha using 1 <;> ext z <;> simp

/-- The second derivative of a scalar forward average converges against fixed energy. -/
theorem c20_scalar_forward_average_second_deriv_integral_limit {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (g : ℝ × Vec d → ℝ)
    (hg : Integrable g (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U))) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U,
      deriv (deriv F) (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) * g z)
      (𝓝[>] 0) (𝓝 (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U,
        deriv (deriv F) (u z) * g z)) := by
  have hF' : ContDiff ℝ 1 (deriv F) := hF.deriv'
  exact c20_integral_bounded_comp_tendsto_in_measure_eventually _ _
    (c20_scalar_forward_average_slab_eventually_aestronglyMeasurable U hU u hu)
    (c20_scalar_forward_average_slab_tendsto_in_measure U hU u hu)
    (deriv (deriv F)) hF'.continuous_deriv_one M hF2 g hg

/-- An L² error tending to zero has vanishing integral against fixed L² data. -/
theorem c20_integral_abs_mul_fixed_L2_tendsto_zero
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    (e : ι → Ω → ℝ) (g : Ω → ℝ)
    (he : ∀ᶠ n in l, MemLp (e n) 2 μ) (hg : MemLp g 2 μ)
    (hlim : Tendsto (fun n => ∫ x, |e n x| ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun n => ∫ x, |e n x| * |g x| ∂μ) l (𝓝 0) := by
  have hsqrt : Tendsto (fun n => Real.sqrt (∫ x, |e n x| ^ 2 ∂μ) *
      Real.sqrt (∫ x, |g x| ^ 2 ∂μ)) l (𝓝 0) := by
    simpa only [Function.comp_def, Real.sqrt_zero, zero_mul] using (Real.continuous_sqrt.continuousAt.tendsto.comp hlim).mul_const
      (Real.sqrt (∫ x, |g x| ^ 2 ∂μ))
  apply squeeze_zero' _ _ hsqrt
  · exact Filter.Eventually.of_forall fun n => integral_nonneg fun x =>
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
  · filter_upwards [he] with n hn
    have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
      (ae_of_all μ fun x => abs_nonneg (e n x))
      (ae_of_all μ fun x => abs_nonneg (g x))
      (show MemLp (fun x => |e n x|) (ENNReal.ofReal 2) μ by
        simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using hn.norm)
      (show MemLp (fun x => |g x|) (ENNReal.ofReal 2) μ by
        simpa only [ENNReal.ofReal_ofNat, Real.norm_eq_abs] using hg.norm)
    simpa only [Real.rpow_two, Real.sqrt_eq_rpow] using hh

/-- The scalar averaging error vanishes in L¹ against the original scalar field. -/
theorem c20_scalar_forward_average_error_mul_field_limit {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U))) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U,
      |h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) - u z| * |u z|)
      (𝓝[>] 0) (𝓝 0) := by
  have hus : MemLp u 2 (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) := by
    apply MemLp.mono_measure (Measure.restrict_mono_set volume ?_) hu
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  refine c20_integral_abs_mul_fixed_L2_tendsto_zero
    (fun h z => h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)) - u z) u ?_ hus ?_
  · have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 / 2 :=
      (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhsmall
    exact c20_scalar_forward_average_slab_memLp U hU u hu (le_of_lt hh) (le_of_lt hhsmall)
  · exact c20_scalar_forward_average_slab_L2 U hU u hu

/-- Quadratic-growth compositions are L¹-continuous under L² convergence. -/
theorem c20_nonlinear_comp_L1_limit
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    {l : Filter ι} (f : ι → Ω → ℝ) (u : Ω → ℝ)
    (he : ∀ᶠ n in l, MemLp (f n - u) 2 μ) (hu : MemLp u 2 μ)
    (hlim : Tendsto (fun n => ∫ x, |f n x - u x| ^ 2 ∂μ) l (𝓝 0))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) :
    Tendsto (fun n => ∫ x, |F (f n x) - F (u x)| ∂μ) l (𝓝 0) := by
  let e : ι → Ω → ℝ := fun n x => f n x - u x
  have h1 : Tendsto (fun n => ∫ x, |e n x| ∂μ) l (𝓝 0) := by
    have h := c20_integral_abs_mul_fixed_L2_tendsto_zero e (fun _ => 1) he
      (memLp_const 1) hlim
    simpa only [abs_one, mul_one] using h
  have h2 : Tendsto (fun n => ∫ x, |e n x| * |u x| ∂μ) l (𝓝 0) :=
    c20_integral_abs_mul_fixed_L2_tendsto_zero e u he hu hlim
  have hupper : Tendsto (fun n => |deriv F 0| * (∫ x, |e n x| ∂μ) +
      (2 * M) * (∫ x, |e n x| * |u x| ∂μ) +
      M * (∫ x, |e n x| ^ 2 ∂μ)) l (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      ((h1.const_mul |deriv F 0|).add (h2.const_mul (2 * M))).add (hlim.const_mul M)
  apply squeeze_zero' _ _ hupper
  · exact Filter.Eventually.of_forall fun n => integral_nonneg fun x => abs_nonneg _
  · filter_upwards [he] with n hn
    change MemLp (e n) 2 μ at hn
    have hE : Integrable (fun x => |e n x|) μ := by
      simpa only [Real.norm_eq_abs] using hn.norm.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    have hEU : Integrable (fun x => |e n x| * |u x|) μ := by
      convert hn.norm.integrable_mul hu.norm using 1 <;> ext x <;> simp [Real.norm_eq_abs]
    have hE2 : Integrable (fun x => |e n x| ^ 2) μ := by
      simpa only [Real.norm_eq_abs] using hn.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hb : (∫ x, |F (f n x) - F (u x)| ∂μ) ≤
        ∫ x, (|deriv F 0| * |e n x| + (2 * M) * (|e n x| * |u x|)) +
          M * |e n x| ^ 2 ∂μ := by
      apply integral_mono_of_nonneg
      · exact Filter.Eventually.of_forall fun x => abs_nonneg _
      · exact ((hE.const_mul _).add (hEU.const_mul _)).add (hE2.const_mul _)
      · filter_upwards with x
        have hi := c20_nonlinear_increment_bound F hF M hM hF2 (u x) (f n x)
        have ht : |f n x| ≤ |u x| + |e n x| := by
          have hv := abs_add_le (u x) (e n x)
          have hh : u x + e n x = f n x := by dsimp [e]; ring
          simpa only [hh] using hv
        have hmul : 0 ≤ |e n x| := abs_nonneg _
        have ht' := mul_le_mul_of_nonneg_left ht hM
        have ht'' := mul_le_mul_of_nonneg_right ht' hmul
        dsimp [e] at hi ht'' ⊢
        nlinarith [sq_nonneg (|f n x - u x|)]
    have hsum := integral_add ((hE.const_mul |deriv F 0|).add (hEU.const_mul (2 * M)))
      (hE2.const_mul M)
    have hsum2 := integral_add (hE.const_mul |deriv F 0|) (hEU.const_mul (2 * M))
    have heq : (∫ x, (|deriv F 0| * |e n x| + (2 * M) * (|e n x| * |u x|)) +
          M * |e n x| ^ 2 ∂μ) =
        |deriv F 0| * (∫ x, |e n x| ∂μ) +
          (2 * M) * (∫ x, |e n x| * |u x| ∂μ) +
          M * (∫ x, |e n x| ^ 2 ∂μ) := by
      simpa only [Pi.add_apply, integral_const_mul] using
        hsum.trans (congrArg (fun t => t + ∫ x, M * |e n x| ^ 2 ∂μ) hsum2)
    exact hb.trans_eq heq

/-- Quadratic growth makes a smooth composition of an L² function integrable. -/
theorem c20_nonlinear_comp_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsFiniteMeasure μ]
    (u : Ω → ℝ) (hu : MemLp u 2 μ)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) :
    Integrable (fun x => F (u x)) μ := by
  have hu1 : Integrable (fun x => |u x|) μ := by
    simpa only [Real.norm_eq_abs] using hu.norm.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
  have hu2 : Integrable (fun x => |u x| ^ 2) μ := by
    simpa only [Real.norm_eq_abs] using hu.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
  have hb : Integrable (fun x => |F 0| + |deriv F 0| * |u x| + M * |u x| ^ 2) μ :=
    ((integrable_const _).add (hu1.const_mul _)).add (hu2.const_mul _)
  apply hb.mono' (hF.continuous.comp_aestronglyMeasurable hu.aestronglyMeasurable)
  filter_upwards with x
  rw [Real.norm_eq_abs]
  have hi := c20_nonlinear_increment_bound F hF M hM hF2 0 (u x)
  have ht := abs_add_le (F (u x) - F 0) (F 0)
  have hs : F (u x) - F 0 + F 0 = F (u x) := by ring
  rw [hs] at ht
  simp only [abs_zero, zero_add, sub_zero] at hi
  nlinarith [abs_nonneg (u x)]

/-- Smooth scalar compositions of the actual forward averages converge in L¹. -/
theorem c20_scalar_forward_average_comp_L1_limit {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U)
    [IsFiniteMeasure ((volume : Measure (ℝ × Vec d)).restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U))]
    (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U,
      |F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) - F (u z)|)
      (𝓝[>] 0) (𝓝 0) := by
  have hus : MemLp u 2 (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) := by
    apply MemLp.mono_measure (Measure.restrict_mono_set volume ?_) hu
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  refine c20_nonlinear_comp_L1_limit
    (μ := (volume : Measure (ℝ × Vec d)).restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U))
    (l := 𝓝[>] (0 : ℝ)) (fun h z => h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) u ?_ hus
    (c20_scalar_forward_average_slab_L2 U hU u hu) F hF M hM hF2
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hhsmall
  exact c20_scalar_forward_average_slab_memLp U hU u hu (le_of_lt hh) (le_of_lt hhsmall)

/-- A bounded measurable weight preserves convergence of integrals under L¹ convergence. -/
theorem c20_weighted_integral_of_L1_limit
    {Ω ι : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter ι}
    (f : ι → Ω → ℝ) (u w : Ω → ℝ) (C : ℝ)
    (hw : AEStronglyMeasurable w μ) (hwb : ∀ᵐ x ∂μ, |w x| ≤ C)
    (hf : ∀ᶠ n in l, Integrable (f n) μ) (hu : Integrable u μ)
    (hlim : Tendsto (fun n => ∫ x, |f n x - u x| ∂μ) l (𝓝 0)) :
    Tendsto (fun n => ∫ x, w x * f n x ∂μ) l
      (𝓝 (∫ x, w x * u x ∂μ)) := by
  have hw' : ∀ᵐ x ∂μ, ‖w x‖ ≤ C := by simpa only [Real.norm_eq_abs] using hwb
  have hui : Integrable (fun x => w x * u x) μ := hu.bdd_mul hw hw'
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [mul_zero] using hlim.const_mul C)
  filter_upwards [hf] with n hn
  have hni : Integrable (fun x => w x * f n x) μ := hn.bdd_mul hw hw'
  have hd : Integrable (fun x => |f n x - u x|) μ := by
    simpa only [Real.norm_eq_abs, Pi.sub_apply] using (hn.sub hu).norm
  have hb : (∫ x, |w x * (f n x - u x)| ∂μ) ≤
      ∫ x, C * |f n x - u x| ∂μ := by
    have hdi : Integrable (fun x => |w x * (f n x - u x)|) μ := by
      simpa only [Real.norm_eq_abs, Pi.sub_apply] using ((hn.sub hu).bdd_mul hw hw').norm
    apply integral_mono_ae hdi (hd.const_mul C)
    filter_upwards [hwb] with x hx
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
  rw [integral_const_mul] at hb
  have hi := abs_integral_le_integral_abs (μ := μ) (f := fun x => w x * (f n x - u x))
  have he : (∫ x, w x * (f n x - u x) ∂μ) =
      (∫ x, w x * f n x ∂μ) - (∫ x, w x * u x ∂μ) := by
    simpa only [mul_sub] using integral_sub hni hui
  rw [he] at hi
  simpa only [Real.norm_eq_abs] using hi.trans hb

/-- Bounded weights preserve the nonlinear forward-average scalar limit. -/
theorem c20_scalar_forward_average_weighted_comp_limit {d : ℕ}
    (U : Set (Vec d)) (hU : MeasurableSet U)
    [IsFiniteMeasure ((volume : Measure (ℝ × Vec d)).restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U))]
    (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (w : ℝ × Vec d → ℝ) (C : ℝ)
    (hw : AEStronglyMeasurable w (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)))
    (hwb : ∀ᵐ z ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U), |w z| ≤ C) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U,
      w z * F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))))
      (𝓝[>] 0) (𝓝 (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U, w z * F (u z))) := by
  let μ := (volume : Measure (ℝ × Vec d)).restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)
  have hus : MemLp u 2 μ := by
    apply MemLp.mono_measure (Measure.restrict_mono_set volume ?_) hu
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hsmall : ∀ᶠ h : ℝ in 𝓝[>] 0, h < 1 / 2 :=
    (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1 / 2)).filter_mono nhdsWithin_le_nhds
  have hfi : ∀ᶠ h : ℝ in 𝓝[>] 0, Integrable
      (fun z => F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2)))) μ := by
    filter_upwards [self_mem_nhdsWithin, hsmall] with h hh hs
    have he := c20_scalar_forward_average_slab_memLp U hU u hu (le_of_lt hh) (le_of_lt hs)
    have hv : MemLp (fun z => h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) 2 μ := by
      convert he.add hus using 1 <;> ext z <;> simp
    exact c20_nonlinear_comp_integrable _ hv F hF M hM hF2
  exact c20_weighted_integral_of_L1_limit
    (μ := μ) (l := 𝓝[>] (0 : ℝ))
    (fun h z => F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))))
    (fun z => F (u z)) w C hw hwb hfi
    (c20_nonlinear_comp_integrable u hus F hF M hM hF2)
    (c20_scalar_forward_average_comp_L1_limit U hU u hu F hF M hM hF2)

/-- The scalar part of the nonlinear limit for the elliptic density and cutoff. -/
theorem c20_elliptic_scalar_forward_average_nonlinear_limit
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : Measurable ψ)
    (hψb : ∀ᵐ z ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r), |ψ z| ≤ 1) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r,
      ρ z.2 * F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) * ψ z)
      (𝓝[>] 0) (𝓝 (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r, ρ z.2 * F (u z) * ψ z)) := by
  let U := EinsteinFull.External.Source.GMP.sourceBall y r
  letI : IsFiniteMeasure ((volume : Measure (ℝ × Vec d)).restrict
      (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) :=
    c18_smallSourceCylinder_isFiniteMeasure y r
  have hw : AEStronglyMeasurable (fun z : ℝ × Vec d => ρ z.2 * ψ z)
      (volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)) :=
    ((hell.1.comp measurable_snd).mul hψ).aestronglyMeasurable
  have hwb : ∀ᵐ z ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U),
      |ρ z.2 * ψ z| ≤ κ⁻¹ := by
    filter_upwards [hψb] with z hz
    have hρ := (hell.2.2 z.2).1
    have hρ' := (hell.2.2 z.2).2.1
    rw [abs_mul, abs_of_pos (lt_of_lt_of_le hκ hρ)]
    calc
      ρ z.2 * |ψ z| ≤ ρ z.2 * 1 := mul_le_mul_of_nonneg_left hz (le_of_lt (lt_of_lt_of_le hκ hρ))
      _ = ρ z.2 := mul_one _
      _ ≤ κ⁻¹ := hρ'
  have h := c20_scalar_forward_average_weighted_comp_limit U
    (c20_sourceBall_measurable y r) u hu F hF M hM hF2
    (fun z => ρ z.2 * ψ z) κ⁻¹ hw hwb
  simpa only [mul_assoc, mul_comm, mul_left_comm] using h

/-- The nonlinear scalar limit for a weighted-caloric solution. -/
theorem c20_caloric_scalar_forward_average_nonlinear_limit
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hcal : EinsteinFull.External.Source.GMP.IsWeightedCaloric ρ α
      (Set.Ioo (-1 : ℝ) 1) (EinsteinFull.External.Source.GMP.sourceBall y r) u G)
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ) (hM : 0 ≤ M)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : Measurable ψ)
    (hψb : ∀ᵐ z ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r), |ψ z| ≤ 1) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r,
      ρ z.2 * F (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) * ψ z)
      (𝓝[>] 0) (𝓝 (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r, ρ z.2 * F (u z) * ψ z)) := by
  exact c20_elliptic_scalar_forward_average_nonlinear_limit hκ ρ α hell y u
    hcal.1 F hF M hM hF2 ψ hψ hψb

/-- Ellipticity and Euclidean L² control make the fixed gradient energy integrable. -/
theorem c20_elliptic_gradient_energy_integrable
    {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (μ : Measure (ℝ × Vec d)) (G : ℝ × Vec d → Vec d)
    (hGm : AEStronglyMeasurable G μ)
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 μ) :
    Integrable (fun z => dot ((α z.2).mulVec (G z)) (G z)) μ := by
  have hs : Integrable (fun z => κ⁻¹ * euclideanNorm (G z) ^ 2) μ := by
    have h := hG.integrable_norm_pow (by norm_num : (2 : ℕ) ≠ 0)
    have hp : Integrable (fun z => euclideanNorm (G z) ^ 2) μ := by
      simpa only [Real.norm_eq_abs, sq_abs] using h
    exact hp.const_mul _
  have hm : AEStronglyMeasurable
      (fun z => dot ((α z.2).mulVec (G z)) (G z)) μ := by
    change AEStronglyMeasurable (fun z => ∑ i : Fin d, (∑ j : Fin d,
      α z.2 i j * G z j) * G z i) μ
    have hm' : AEStronglyMeasurable (∑ i : Fin d, fun z => (∑ j : Fin d,
        α z.2 i j * G z j) * G z i) μ := by
      apply Finset.aestronglyMeasurable_sum
      intro i hi
      apply AEStronglyMeasurable.mul _ ((continuous_apply i).comp_aestronglyMeasurable hGm)
      have hjm : AEStronglyMeasurable (∑ j : Fin d, fun z => α z.2 i j * G z j) μ := by
        apply Finset.aestronglyMeasurable_sum
        intro j hj
        apply AEStronglyMeasurable.mul _ ((continuous_apply j).comp_aestronglyMeasurable hGm)
        let : MeasurableSpace (Mat d) := EinsteinRelation.instMeasurableSpaceMat d
        let : BorelSpace (Mat d) := EinsteinRelation.instBorelSpaceMat d
        exact ((((continuous_id : Continuous (id : Mat d → Mat d)).matrix_elem i j).measurable.comp
          hell.2.1).comp measurable_snd).aestronglyMeasurable
      convert hjm using 1
      ext z
      simp only [Finset.sum_apply]
    convert hm' using 1
    ext z
    simp only [Finset.sum_apply]
  apply hs.mono' hm
  filter_upwards with z
  have hsq : 0 ≤ euclideanSq (G z) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hq := (hell.2.2 z.2).2.2.2 (G z)
  have hcomm : dot ((α z.2).mulVec (G z)) (G z) =
      dot (G z) ((α z.2).mulVec (G z)) := by
    unfold dot
    apply Finset.sum_congr rfl
    intro i hi
    exact mul_comm _ _
  rw [Real.norm_eq_abs, hcomm, abs_of_nonneg (le_trans (mul_nonneg hκ.le hsq) hq.1)]
  unfold euclideanNorm
  rw [Real.sq_sqrt hsq]
  exact hq.2

/-- The second-derivative multiplier converges against the fixed weighted energy. -/
theorem c20_scalar_forward_average_fixed_energy_limit
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M)
    (ψ : ℝ × Vec d → ℝ) (hψ : Measurable ψ)
    (hψb : ∀ᵐ z ∂volume.restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r), |ψ z| ≤ 1) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r,
      deriv (deriv F) (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) *
        dot ((α z.2).mulVec (G z)) (G z) * ψ z)
      (𝓝[>] 0) (𝓝 (∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
        EinsteinFull.External.Source.GMP.sourceBall y r,
        deriv (deriv F) (u z) * dot ((α z.2).mulVec (G z)) (G z) * ψ z)) := by
  let U := EinsteinFull.External.Source.GMP.sourceBall y r
  let μ := (volume : Measure (ℝ × Vec d)).restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)
  have hμ : μ ≤ volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U) := by
    apply Measure.restrict_mono_set
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have hgs : MemLp (fun z => euclideanNorm (G z)) 2 μ := hG.mono_measure hμ
  have hgms : AEStronglyMeasurable G μ := hGm.mono_measure hμ
  have he : Integrable (fun z => dot ((α z.2).mulVec (G z)) (G z)) μ :=
    c20_elliptic_gradient_energy_integrable hκ ρ α hell μ G hgms hgs
  have hb : ∀ᵐ z ∂μ, ‖ψ z‖ ≤ (1 : ℝ) := by
    simpa only [Real.norm_eq_abs] using hψb
  have hw : Integrable (fun z => dot ((α z.2).mulVec (G z)) (G z) * ψ z) μ :=
    he.mul_bdd hψ.aestronglyMeasurable hb
  have h := c20_scalar_forward_average_second_deriv_integral_limit U
    (c20_sourceBall_measurable y r) u hu F hF M hF2
    (fun z => dot ((α z.2).mulVec (G z)) (G z) * ψ z) hw
  simpa only [mul_assoc] using h

/-- The second-derivative multiplier converges in L¹ against fixed gradient energy. -/
theorem c20_scalar_forward_average_fixed_energy_abs_limit
    {d : ℕ} {κ r : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (y : Vec d) (u : ℝ × Vec d → ℝ) (G : ℝ × Vec d → Vec d)
    (hu : MemLp u 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hGm : AEStronglyMeasurable G (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (hG : MemLp (fun z => euclideanNorm (G z)) 2 (volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r)))
    (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (M : ℝ)
    (hF2 : ∀ s, |deriv (deriv F) s| ≤ M) :
    Tendsto (fun h : ℝ => ∫ z in Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ
      EinsteinFull.External.Source.GMP.sourceBall y r,
      |deriv (deriv F) (h⁻¹ * (∫ s in (0 : ℝ)..h, u (z.1 + s, z.2))) -
        deriv (deriv F) (u z)| * |dot ((α z.2).mulVec (G z)) (G z)|)
      (𝓝[>] 0) (𝓝 0) := by
  let U := EinsteinFull.External.Source.GMP.sourceBall y r
  let μ := (volume : Measure (ℝ × Vec d)).restrict (Set.Ioo (-(1 / 2 : ℝ)) (1 / 2) ×ˢ U)
  have hμ : μ ≤ volume.restrict (Set.Ioo (-1 : ℝ) 1 ×ˢ U) := by
    apply Measure.restrict_mono_set
    intro z hz
    exact ⟨⟨by linarith [hz.1.1], by linarith [hz.1.2]⟩, hz.2⟩
  have he : Integrable (fun z => dot ((α z.2).mulVec (G z)) (G z)) μ :=
    c20_elliptic_gradient_energy_integrable hκ ρ α hell μ G
      (hGm.mono_measure hμ) (hG.mono_measure hμ)
  have hF' : ContDiff ℝ 1 (deriv F) := hF.deriv'
  exact c20_integral_abs_bounded_comp_tendsto_in_measure _ _
    (c20_scalar_forward_average_slab_eventually_aestronglyMeasurable U
      (c20_sourceBall_measurable y r) u hu)
    ((hu.mono_measure hμ).aestronglyMeasurable)
    (c20_scalar_forward_average_slab_tendsto_in_measure U
      (c20_sourceBall_measurable y r) u hu)
    (deriv (deriv F)) hF'.continuous_deriv_one M hF2 _ he

/-- An elliptic coefficient matrix is positive definite. -/
theorem c20_elliptic_matrix_posDef {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (x : Vec d) : (α x).PosDef := by
  apply Matrix.posDef_iff_dotProduct_mulVec.mpr
  constructor
  · change Matrix.conjTranspose (α x) = α x
    ext i j
    change star (α x j i) = α x i j
    rw [star_trivial]
    exact congrFun (congrFun (hell.2.2 x).2.2.1 i) j
  · intro v hv
    have hv' : ∃ i, v i ≠ 0 := by
      by_contra h
      push_neg at h
      apply hv
      funext i
      simpa using h i
    obtain ⟨i, hi⟩ := hv'
    have hsq : 0 < euclideanSq v := by
      unfold euclideanSq dot
      have hp : 0 < v i * v i := mul_self_pos.mpr hi
      exact lt_of_lt_of_le hp (Finset.single_le_sum
        (fun j _ => mul_self_nonneg (v j)) (Finset.mem_univ i))
    have hl := ((hell.2.2 x).2.2.2 v).1
    have hp : 0 < dot v ((α x).mulVec v) := lt_of_lt_of_le (mul_pos hκ hsq) hl
    simpa only [star_trivial, dot, dotProduct] using hp

/-- The elliptic bilinear form is bounded by the Euclidean product norm. -/
theorem c20_elliptic_bilinear_bound {d : ℕ} {κ : ℝ} (hκ : 0 < κ)
    (ρ : Vec d → ℝ) (α : Vec d → Mat d)
    (hell : EinsteinFull.External.Source.GMP.IsUniformlyElliptic κ ρ α)
    (x u v : Vec d) :
    |dot u ((α x).mulVec v)| ≤ κ⁻¹ * euclideanNorm u * euclideanNorm v := by
  have hp := (c20_elliptic_matrix_posDef hκ ρ α hell x).star_dotProduct_mulVec_mul_le u v
  have hp' : (dot u ((α x).mulVec v)) ^ 2 ≤
      dot u ((α x).mulVec u) * dot v ((α x).mulVec v) := by
    simpa only [star_trivial, dot, dotProduct, pow_two] using hp
  have hs (w : Vec d) : 0 ≤ euclideanSq w := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  have hn (w : Vec d) : 0 ≤ euclideanNorm w := Real.sqrt_nonneg _
  have he (w : Vec d) : euclideanNorm w ^ 2 = euclideanSq w := by
    unfold euclideanNorm
    exact Real.sq_sqrt (hs w)
  have hq1 := ((hell.2.2 x).2.2.2 u)
  have hq2 := ((hell.2.2 x).2.2.2 v)
  have hq2nonneg : 0 ≤ dot v ((α x).mulVec v) :=
    (mul_nonneg hκ.le (hs v)).trans hq2.1
  have hk : 0 ≤ κ⁻¹ := le_of_lt (inv_pos.mpr hκ)
  have hmul := mul_le_mul hq1.2 hq2.2 hq2nonneg (mul_nonneg hk (hs u))
  rw [← he u, ← he v] at hmul
  have hab : 0 ≤ |dot u ((α x).mulVec v)| := abs_nonneg _
  have hright : 0 ≤ κ⁻¹ * euclideanNorm u * euclideanNorm v :=
    mul_nonneg (mul_nonneg hk (hn u)) (hn v)
  nlinarith [sq_abs (dot u ((α x).mulVec v))]

end EinsteinFull.Calculus
