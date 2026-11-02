import EinsteinRelation.Correctors.HeatSmoothing
import EinsteinRelation.Probability.LocalSigma
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# `L^m` contraction of the Euclidean heat smoothing

For a stationary probability law `Q` on coefficient pairs and `1 ≤ m`, the smoothing
`H_t f = heatSmoothed t f` is a contraction of `L^m(Q)`. The proof writes the smoothing as an
integral against the probability density `p_t = euclideanHeatKernel t`. The `m`-th power of
`H_t f(ω)` is bounded by the `p_t`-average of `|f(T_z ω)|^m` (Jensen in lintegral form), and
Tonelli together with stationarity removes the translation.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-! ### Facts about the heat kernel

Nonnegativity, integrability, and unit mass of `euclideanHeatKernel` for `t > 0`. -/

private theorem continuous_euclideanSq : Continuous (fun x : Vec d => euclideanSq x) := by
  unfold euclideanSq dot
  exact continuous_finset_sum _ fun i _ => (continuous_apply i).mul (continuous_apply i)

private theorem measurable_euclideanHeatKernel (t : ℝ) :
    Measurable (euclideanHeatKernel (d := d) t) := by
  unfold euclideanHeatKernel
  exact measurable_const.mul
    (Real.continuous_exp.measurable.comp (continuous_euclideanSq.neg.div_const (4 * t)).measurable)

private theorem euclideanHeatKernel_nonneg {t : ℝ} (ht : 0 ≤ t) (x : Vec d) :
    0 ≤ euclideanHeatKernel t x := by
  unfold euclideanHeatKernel
  exact mul_nonneg (Real.rpow_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) ht) _)
    (Real.exp_pos _).le

private theorem exp_gauss_eq (t x : ℝ) :
    Real.exp (-(x * x) / (4 * t)) = Real.exp (-(1 / (4 * t)) * x ^ 2) := by
  congr 1
  ring

private theorem integral_exp_gauss (t : ℝ) :
    ∫ x : ℝ, Real.exp (-(x * x) / (4 * t)) = Real.sqrt (4 * Real.pi * t) := by
  simp only [exp_gauss_eq t]
  rw [integral_gaussian, div_div_eq_mul_div, div_one]
  congr 1
  ring

private theorem rpow_neg_half_mul_sqrt_pow {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x ^ (-(n : ℝ) / 2) * Real.sqrt x ^ n = 1 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx.le, ← Real.rpow_add hx]
  have h : -(n : ℝ) / 2 + 1 / 2 * (n : ℝ) = 0 := by ring
  rw [h, Real.rpow_zero]

private theorem euclideanHeatKernel_eq_prod (t : ℝ) (z : Vec d) :
    euclideanHeatKernel t z =
      (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * ∏ i, Real.exp (-(z i * z i) / (4 * t)) := by
  have hsum : -(euclideanSq z) / (4 * t) = ∑ i, -(z i * z i) / (4 * t) := by
    simp only [euclideanSq, dot, neg_div, Finset.sum_div, Finset.sum_neg_distrib]
  unfold euclideanHeatKernel
  rw [← Real.exp_sum, hsum]

private theorem integral_euclideanHeatKernel {t : ℝ} (ht : 0 < t) :
    ∫ z : Vec d, euclideanHeatKernel t z = 1 := by
  simp only [euclideanHeatKernel_eq_prod]
  rw [integral_const_mul,
    integral_fintype_prod_volume_eq_prod (fun (_ : Fin d) (x : ℝ) => Real.exp (-(x * x) / (4 * t)))]
  simp only [integral_exp_gauss t, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  exact rpow_neg_half_mul_sqrt_pow (mul_pos (mul_pos (by norm_num : (0 : ℝ) < 4) Real.pi_pos) ht) d

private theorem integrable_euclideanHeatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (euclideanHeatKernel (d := d) t) := by
  have hg : Integrable (fun x : ℝ => Real.exp (-(x * x) / (4 * t))) := by
    refine (integrable_exp_neg_mul_sq (b := 1 / (4 * t)) (one_div_pos.mpr (by linarith))).congr
      (ae_of_all _ fun x => ?_)
    exact (exp_gauss_eq t x).symm
  have hprod : Integrable (fun z : Vec d => ∏ i, Real.exp (-(z i * z i) / (4 * t))) := by
    rw [volume_pi]
    exact Integrable.fintype_prod (f := fun (_ : Fin d) (x : ℝ) => Real.exp (-(x * x) / (4 * t)))
      (μ := fun _ => (volume : Measure ℝ)) (fun _ => hg)
  have hfun : euclideanHeatKernel (d := d) t = fun z : Vec d =>
      (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * ∏ i, Real.exp (-(z i * z i) / (4 * t)) :=
    funext (euclideanHeatKernel_eq_prod t)
  rw [hfun]
  exact hprod.const_mul _

private theorem lintegral_ofReal_heatKernel {t : ℝ} (ht : 0 < t) :
    ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) = 1 := by
  rw [← ofReal_integral_eq_lintegral_ofReal (integrable_euclideanHeatKernel (d := d) ht)
    (ae_of_all _ fun z => euclideanHeatKernel_nonneg ht.le z),
    integral_euclideanHeatKernel ht, ENNReal.ofReal_one]

/-- The heat kernel has unit mass, so `p_t(z) dz` is a probability measure. -/
private theorem heatDensity_univ {t : ℝ} (ht : 0 < t) :
    ((volume : Measure (Vec d)).withDensity fun z => ENNReal.ofReal (euclideanHeatKernel t z))
      Set.univ = 1 := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    lintegral_ofReal_heatKernel (d := d) ht]

private theorem lintegral_heatDensity {t : ℝ} {G : Vec d → ℝ≥0∞} (hG : Measurable G) :
    ∫⁻ z, G z ∂((volume : Measure (Vec d)).withDensity
        fun z => ENNReal.ofReal (euclideanHeatKernel t z)) =
      ∫⁻ z, ENNReal.ofReal (euclideanHeatKernel t z) * G z :=
  lintegral_withDensity_eq_lintegral_mul _
    (measurable_euclideanHeatKernel (d := d) t).ennreal_ofReal hG

/-! ### Jensen's inequality in lintegral form -/

/-- For a probability measure and `1 ≤ m`, `(∫ G)^m ≤ ∫ G^m` in `ℝ≥0∞`. -/
private theorem lintegral_rpow_le_of_univ {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (hμ : μ Set.univ = 1) {m : ℝ} (hm : 1 ≤ m) {G : α → ℝ≥0∞} (hG : Measurable G) :
    (∫⁻ a, G a ∂μ) ^ m ≤ ∫⁻ a, G a ^ m ∂μ := by
  rcases hm.eq_or_lt with h1 | h1
  · rw [← h1]
    simp
  · have hpq := Real.HolderConjugate.conjExponent h1
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hpq hG.aemeasurable
      (measurable_const : Measurable fun _ : α => (1 : ℝ≥0∞)).aemeasurable
    simp only [Pi.mul_apply, mul_one, lintegral_const, hμ, one_mul, ENNReal.one_rpow] at h
    have hm0 : m ≠ 0 := (zero_lt_one.trans h1).ne'
    have hpow := ENNReal.rpow_le_rpow h (zero_le_one.trans hm)
    rwa [← ENNReal.rpow_mul, one_div_mul_cancel hm0, ENNReal.rpow_one] at hpow

/-! ### Translation measurability and the pointwise Jensen bound -/

private theorem heatSmoothed_of_ne {t : ℝ} (ht : t ≠ 0) (f : FieldPair d → ℝ) (ω : FieldPair d) :
    heatSmoothed t f ω =
      ∫ z : Vec d, euclideanHeatKernel t z * f (translate z ω) ∂(volume : Measure (Vec d)) := by
  unfold heatSmoothed
  rw [if_neg ht]

private theorem measurable_translate_point (ω : FieldPair d) :
    Measurable (fun z : Vec d => translate z ω) := by
  have hc : Continuous (fun z : Vec d => (z, ω)) := continuous_id.prodMk continuous_const
  exact (Probability.continuous_translate.comp hc).measurable

private theorem measurable_translate_swap :
    Measurable (fun p : FieldPair d × Vec d => translate p.2 p.1) :=
  Probability.continuous_translate.measurable.comp measurable_swap

private theorem measurable_heatWeight {f : FieldPair d → ℝ} (hf : Measurable f) (t m : ℝ) :
    Measurable (fun p : FieldPair d × Vec d =>
      ENNReal.ofReal (euclideanHeatKernel t p.2) * ‖f (translate p.2 p.1)‖ₑ ^ m) :=
  ((measurable_euclideanHeatKernel (d := d) t).comp measurable_snd).ennreal_ofReal.mul
    ((hf.comp measurable_translate_swap).enorm.pow_const m)

/-- Stationarity: the `ℝ≥0∞`-valued integral of a translated observable is unchanged. -/
private theorem lintegral_translate_eq {Q : Measure (FieldPair d)}
    (hQ : EinsteinRelation.IsStationary Q) {F : FieldPair d → ℝ≥0∞} (hF : Measurable F)
    (z : Vec d) : ∫⁻ ω, F (translate z ω) ∂Q = ∫⁻ ω, F ω ∂Q := by
  rw [← lintegral_map hF (Probability.measurable_translate z), hQ z]

/-- The `m`-th power moment of the smoothed field is bounded by the stationary `m`-th
moment of `f`, through the heat-kernel weight and Tonelli. -/
private theorem lintegral_heatWeight_eq (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : EinsteinRelation.IsStationary Q) {f : FieldPair d → ℝ} (hf : Measurable f) {t : ℝ}
    (ht : 0 < t) (m : ℝ) :
    ∫⁻ ω, ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * ‖f (translate z ω)‖ₑ ^ m
        ∂(volume : Measure (Vec d)) ∂Q = ∫⁻ ω, ‖f ω‖ₑ ^ m ∂Q := by
  have hFm : Measurable (fun ω : FieldPair d => ‖f ω‖ₑ ^ m) := hf.enorm.pow_const m
  have hKf : Measurable (fun z : Vec d => ENNReal.ofReal (euclideanHeatKernel t z)) :=
    (measurable_euclideanHeatKernel (d := d) t).ennreal_ofReal
  calc ∫⁻ ω, ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * ‖f (translate z ω)‖ₑ ^ m
          ∂(volume : Measure (Vec d)) ∂Q
      = ∫⁻ z : Vec d, ∫⁻ ω, ENNReal.ofReal (euclideanHeatKernel t z) * ‖f (translate z ω)‖ₑ ^ m
          ∂Q ∂(volume : Measure (Vec d)) :=
        lintegral_lintegral_swap (measurable_heatWeight hf t m).aemeasurable
    _ = ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * ∫⁻ ω, ‖f ω‖ₑ ^ m ∂Q
          ∂(volume : Measure (Vec d)) := by
        refine lintegral_congr fun z => ?_
        rw [lintegral_const_mul' (ENNReal.ofReal (euclideanHeatKernel t z)) _ ENNReal.ofReal_ne_top,
          lintegral_translate_eq hQ hFm z]
    _ = (∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) ∂(volume : Measure (Vec d)))
          * ∫⁻ ω, ‖f ω‖ₑ ^ m ∂Q := lintegral_mul_const _ hKf
    _ = ∫⁻ ω, ‖f ω‖ₑ ^ m ∂Q := by
        rw [lintegral_ofReal_heatKernel (d := d) ht, one_mul]

/-- Pointwise Jensen bound: `|H_t f(ω)|^m ≤ ∫ p_t(z) |f(T_z ω)|^m dz` for `t > 0`. -/
private theorem heatSmoothed_enorm_rpow_le {t : ℝ} (ht : 0 < t) {f : FieldPair d → ℝ}
    (hf : Measurable f) {m : ℝ} (hm : 1 ≤ m) (ω : FieldPair d) :
    ‖heatSmoothed t f ω‖ₑ ^ m ≤
      ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * ‖f (translate z ω)‖ₑ ^ m := by
  have hG : Measurable (fun z : Vec d => ‖f (translate z ω)‖ₑ) :=
    (hf.comp (measurable_translate_point ω)).enorm
  have hnorm : ‖heatSmoothed t f ω‖ₑ ≤
      ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * ‖f (translate z ω)‖ₑ := by
    rw [heatSmoothed_of_ne ht.ne' f ω]
    refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq (lintegral_congr fun z => ?_))
    rw [enorm_mul, Real.enorm_eq_ofReal (euclideanHeatKernel_nonneg ht.le z)]
  have h1 := lintegral_heatDensity (t := t) hG
  have h2 := lintegral_heatDensity (t := t) (hG.pow_const m)
  have hjensen := lintegral_rpow_le_of_univ _ (heatDensity_univ (d := d) ht) hm hG
  rw [h1, h2] at hjensen
  exact (ENNReal.rpow_le_rpow hnorm (zero_le_one.trans hm)).trans hjensen

/-- The `t > 0` case of the `L^m` contraction, in lintegral form. -/
private theorem lintegral_heatSmoothed_rpow_le (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : EinsteinRelation.IsStationary Q) {f : FieldPair d → ℝ} (hf : Measurable f) {t : ℝ}
    (ht : 0 < t) {m : ℝ} (hm : 1 ≤ m) :
    ∫⁻ ω, ‖heatSmoothed t f ω‖ₑ ^ m ∂Q ≤ ∫⁻ ω, ‖f ω‖ₑ ^ m ∂Q :=
  calc ∫⁻ ω, ‖heatSmoothed t f ω‖ₑ ^ m ∂Q
      ≤ ∫⁻ ω, ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * ‖f (translate z ω)‖ₑ ^ m
          ∂(volume : Measure (Vec d)) ∂Q :=
        lintegral_mono fun ω => heatSmoothed_enorm_rpow_le ht hf hm ω
    _ = ∫⁻ ω, ‖f ω‖ₑ ^ m ∂Q := lintegral_heatWeight_eq Q hQ hf ht m

/-- Measurability of the smoothed field. -/
private theorem measurable_heatSmoothed {t : ℝ} (ht : 0 ≤ t) {f : FieldPair d → ℝ}
    (hf : Measurable f) : Measurable (heatSmoothed t f) := by
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    have hid : heatSmoothed 0 f = f := funext fun ω => by simp [heatSmoothed]
    rw [hid]
    exact hf
  · have hfun : heatSmoothed t f = fun ω =>
        ∫ z : Vec d, euclideanHeatKernel t z * f (translate z ω) ∂(volume : Measure (Vec d)) :=
      funext fun ω => heatSmoothed_of_ne htpos.ne' f ω
    have hint : Measurable (fun p : FieldPair d × Vec d =>
        euclideanHeatKernel t p.2 * f (translate p.2 p.1)) :=
      ((measurable_euclideanHeatKernel (d := d) t).comp measurable_snd).mul
        (hf.comp measurable_translate_swap)
    rw [hfun]
    exact (MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := (volume : Measure (Vec d)))
      hint.stronglyMeasurable).measurable

/-! ### Public results -/

/-- **Contraction of `H_t` on `L^m(Q)`.** For a stationary probability law `Q`, a measurable
field `f`, and `1 ≤ m`, the smoothing `H_t f` (`t ≥ 0`) does not increase the `L^m(Q)` norm. -/
theorem eLpNorm_heatSmoothed_le (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : EinsteinRelation.IsStationary Q) {m : ℝ} (hm : 1 ≤ m) {f : FieldPair d → ℝ}
    (hf : Measurable f) {t : ℝ} (ht : 0 ≤ t) :
    eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) Q ≤ eLpNorm f (ENNReal.ofReal m) Q := by
  have hm0 : (0 : ℝ) ≤ m := zero_le_one.trans hm
  have hp0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hm)).ne'
  have hpt : ENNReal.ofReal m ≠ ∞ := ENNReal.ofReal_ne_top
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    have hid : heatSmoothed 0 f = f := funext fun ω => by simp [heatSmoothed]
    exact le_of_eq (by rw [hid])
  · rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt
        (measurable_heatSmoothed ht hf).aestronglyMeasurable,
      eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hpt hf.aestronglyMeasurable,
      ENNReal.toReal_ofReal hm0]
    exact ENNReal.rpow_le_rpow (lintegral_heatSmoothed_rpow_le Q hQ hf htpos hm)
      (one_div_nonneg.mpr hm0)

/-- Translation of a difference: for a fixed `ω` with both orbit integrals integrable,
`H_t (f - g)(ω) = H_t f(ω) - H_t g(ω)`. -/
private theorem heatSmoothed_sub_of_integrable {t : ℝ} (ht : t ≠ 0) (f g : FieldPair d → ℝ)
    (ω : FieldPair d)
    (hfi : Integrable (fun z : Vec d => euclideanHeatKernel t z * f (translate z ω)))
    (hgi : Integrable (fun z : Vec d => euclideanHeatKernel t z * g (translate z ω))) :
    heatSmoothed t (f - g) ω = heatSmoothed t f ω - heatSmoothed t g ω := by
  simp only [heatSmoothed_of_ne ht]
  rw [← integral_sub hfi hgi]
  congr 1
  funext z
  simp only [Pi.sub_apply, mul_sub]

/-- An orbit integrand is integrable once its weighted `L^1` norm is finite. -/
private theorem integrable_heat_integrand {t : ℝ} (ht : 0 ≤ t) {f : FieldPair d → ℝ}
    (hf : Measurable f) (ω : FieldPair d)
    (hfin : ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * ‖f (translate z ω)‖ₑ < ∞) :
    Integrable (fun z : Vec d => euclideanHeatKernel t z * f (translate z ω)) := by
  have hconv : ∫⁻ z : Vec d, ‖euclideanHeatKernel t z * f (translate z ω)‖ₑ
      = ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * ‖f (translate z ω)‖ₑ :=
    lintegral_congr fun z => by
      rw [enorm_mul, Real.enorm_eq_ofReal (euclideanHeatKernel_nonneg ht z)]
  refine ⟨((measurable_euclideanHeatKernel (d := d) t).mul
    (hf.comp (measurable_translate_point ω))).aestronglyMeasurable, ?_⟩
  show ∫⁻ z : Vec d, ‖euclideanHeatKernel t z * f (translate z ω)‖ₑ < ∞
  rw [hconv]
  exact hfin

/-- A first-moment bound from the `m`-th moment bound for the heat density. -/
private theorem lintegral_heat_lt_top {t : ℝ} (ht : 0 < t) {G : Vec d → ℝ≥0∞}
    (hG : Measurable G) {m : ℝ} (hm : 1 ≤ m)
    (h : ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * G z ^ m < ∞) :
    ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * G z < ∞ := by
  have h1 := lintegral_rpow_le_of_univ _ (heatDensity_univ (d := d) ht) hm hG
  rw [lintegral_heatDensity (t := t) hG, lintegral_heatDensity (t := t) (hG.pow_const m)] at h1
  by_contra hX
  rw [not_lt, top_le_iff] at hX
  rw [hX, ENNReal.top_rpow_of_pos (zero_lt_one.trans_le hm)] at h1
  exact lt_irrefl _ (lt_of_le_of_lt h1 h)

/-- For `Q`-a.e. `ω`, the orbit integral of `|f|` against the heat kernel is finite whenever
`f ∈ L^m(Q)`. -/
private theorem heat_integrable_ae (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : EinsteinRelation.IsStationary Q) {m : ℝ} (hm : 1 ≤ m) {f : FieldPair d → ℝ}
    (hf : Measurable f) (hfm : MemLp f (ENNReal.ofReal m) Q) {t : ℝ} (ht : 0 < t) :
    ∀ᵐ ω ∂Q, ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * ‖f (translate z ω)‖ₑ < ∞ := by
  have hp0 : ENNReal.ofReal m ≠ 0 := (ENNReal.ofReal_pos.mpr (zero_lt_one.trans_le hm)).ne'
  have hpt : ENNReal.ofReal m ≠ ∞ := ENNReal.ofReal_ne_top
  have hfin : ∫⁻ ω, ‖f ω‖ₑ ^ m ∂Q ≠ ∞ := by
    have h := (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top hp0 hpt
      hf.aestronglyMeasurable).mp hfm.eLpNorm_lt_top
    rw [ENNReal.toReal_ofReal (zero_le_one.trans hm)] at h
    exact h.ne
  have hΦfin : ∫⁻ ω, ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * ‖f (translate z ω)‖ₑ ^ m
      ∂(volume : Measure (Vec d)) ∂Q ≠ ∞ := by
    rw [lintegral_heatWeight_eq Q hQ hf ht m]
    exact hfin
  have hΦmeas : Measurable (fun ω : FieldPair d =>
      ∫⁻ z : Vec d, ENNReal.ofReal (euclideanHeatKernel t z) * ‖f (translate z ω)‖ₑ ^ m
        ∂(volume : Measure (Vec d))) :=
    (measurable_heatWeight hf t m).lintegral_prod_right'
  filter_upwards [ae_lt_top hΦmeas hΦfin] with ω hω
  exact lintegral_heat_lt_top ht ((hf.comp (measurable_translate_point ω)).enorm) hm hω

/-- For `t > 0` and `f, g ∈ L^m(Q)`, the smoothing is additive `Q`-a.e. in the field. -/
theorem heatSmoothed_sub_ae (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : EinsteinRelation.IsStationary Q) {m : ℝ} (hm : 1 ≤ m) {f g : FieldPair d → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfm : MemLp f (ENNReal.ofReal m) Q)
    (hgm : MemLp g (ENNReal.ofReal m) Q) {t : ℝ} (ht : 0 ≤ t) :
    heatSmoothed t (f - g) =ᵐ[Q] heatSmoothed t f - heatSmoothed t g := by
  rcases ht.eq_or_lt with h0 | htpos
  · subst h0
    exact ae_of_all Q fun ω => by simp [heatSmoothed]
  · filter_upwards [heat_integrable_ae Q hQ hm hf hfm htpos,
      heat_integrable_ae Q hQ hm hg hgm htpos] with ω hω1 hω2
    exact heatSmoothed_sub_of_integrable htpos.ne' f g ω
      (integrable_heat_integrand htpos.le hf ω hω1) (integrable_heat_integrand htpos.le hg ω hω2)

/-- **Approximation step for `H_t`.** If `H_t g` and `f - g` are controlled in `L^m(Q)`, then
so is `H_t f`, with the sum of the two bounds. -/
theorem eLpNorm_heatSmoothed_le_of_approx (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : EinsteinRelation.IsStationary Q) {m : ℝ} (hm : 1 ≤ m) {f g : FieldPair d → ℝ}
    (hf : Measurable f) (hg : Measurable g) (hfm : MemLp f (ENNReal.ofReal m) Q)
    (hgm : MemLp g (ENNReal.ofReal m) Q) {t : ℝ} (ht : 0 ≤ t) {A B R : ℝ} (hA : 0 ≤ A)
    (hB : 0 ≤ B) (hR : 0 < R)
    (hG : eLpNorm (heatSmoothed t g) (ENNReal.ofReal m) Q
      ≤ ENNReal.ofReal (A * (Real.sqrt (1 + t))⁻¹))
    (hFG : eLpNorm (f - g) (ENNReal.ofReal m) Q ≤ ENNReal.ofReal (B * R⁻¹)) :
    eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) Q
      ≤ ENNReal.ofReal ((A + B) * ((Real.sqrt (1 + t))⁻¹ + R⁻¹)) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal m := ENNReal.one_le_ofReal.mpr hm
  have hfg : Measurable (f - g) := hf.sub hg
  have hsplit : heatSmoothed t f =ᵐ[Q] heatSmoothed t g + heatSmoothed t (f - g) := by
    filter_upwards [heatSmoothed_sub_ae Q hQ hm hf hg hfm hgm ht] with ω hω
    simp only [Pi.add_apply, hω, Pi.sub_apply]
    ring
  have ha : 0 ≤ (Real.sqrt (1 + t))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hb : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  have hAa : 0 ≤ A * (Real.sqrt (1 + t))⁻¹ := mul_nonneg hA ha
  have hBb : 0 ≤ B * R⁻¹ := mul_nonneg hB hb
  calc eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) Q
      = eLpNorm (heatSmoothed t g + heatSmoothed t (f - g)) (ENNReal.ofReal m) Q :=
        eLpNorm_congr_ae hsplit
    _ ≤ eLpNorm (heatSmoothed t g) (ENNReal.ofReal m) Q
          + eLpNorm (heatSmoothed t (f - g)) (ENNReal.ofReal m) Q :=
        eLpNorm_add_le hp1
    _ ≤ ENNReal.ofReal (A * (Real.sqrt (1 + t))⁻¹) + ENNReal.ofReal (B * R⁻¹) :=
        add_le_add hG ((eLpNorm_heatSmoothed_le Q hQ hm hfg ht).trans hFG)
    _ = ENNReal.ofReal (A * (Real.sqrt (1 + t))⁻¹ + B * R⁻¹) :=
        (ENNReal.ofReal_add hAa hBb).symm
    _ ≤ ENNReal.ofReal ((A + B) * ((Real.sqrt (1 + t))⁻¹ + R⁻¹)) :=
        ENNReal.ofReal_le_ofReal (by nlinarith [mul_nonneg hA hb, mul_nonneg hB ha])

end EinsteinRelation.Correctors

end
