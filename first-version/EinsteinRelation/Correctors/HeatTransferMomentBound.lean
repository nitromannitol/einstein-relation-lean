import EinsteinRelation.Correctors.HeatConvolutionMeasurability
import EinsteinRelation.Correctors.HeatDecayTimeIntegral
import EinsteinRelation.Correctors.TimeIntegralLpBound

/-! # Moment estimates for heat-transfer integrals

Source: `paper/main.tex:1030–1041`. The averaging assumption controls the
time integral of a spatial convolution by `3 A M r`, where `A` bounds the
kernel's `L¹` mass. This supplies the time-integral estimate in Step 2.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- Time integration of the scalar averaging estimate after convolution
with any integrable spatial kernel (`paper/main.tex:1033–1041`). -/
theorem eLpNorm_integral_heatConvolution_le {Q : Measure (FieldPair d)} [SFinite Q]
    (hQ : IsStationary Q) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {K : Vec d → ℝ} (hK : Measurable K) (hKi : Integrable K volume)
    {A M r R : ℝ} (hA : 0 < A) (hM : 0 < M) (hr : 0 < r)
    (hR : 0 < R) (hrR : r ≤ R) (hKA : (∫ z, |K z|) ≤ A)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hheat : ∀ t : ℝ, 0 ≤ t →
      eLpNorm (heatSmoothed t f) p Q ≤
        ENNReal.ofReal (M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹))) :
    eLpNorm (fun ω => ∫ t in (0 : ℝ)..r ^ 2,
      horizontalMollify K (heatSmoothed t f) ω) p Q ≤ ENNReal.ofReal (3 * A * M * r) := by
  let B : ℝ → ℝ := fun t => A * M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹)
  have hB : Measurable B := measurable_const.mul
    (((continuous_const.add continuous_id).sqrt.measurable.inv).add measurable_const)
  have hBc : ContinuousOn B (Set.Icc 0 (r ^ 2)) :=
    continuousOn_const.mul ((continuousOn_inv_sqrt_one_add _).add continuousOn_const)
  have hBi : IntervalIntegrable B volume 0 (r ^ 2) :=
    hBc.intervalIntegrable_of_Icc (sq_nonneg r)
  have hBpos (t : ℝ) : 0 < B t :=
    mul_pos (mul_pos hA hM)
      (add_pos_of_nonneg_of_pos (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_pos.mpr hR))
  have hmass : 0 < ∫ t in Set.Ioc (0 : ℝ) (r ^ 2), B t := by
    rw [← intervalIntegral.integral_of_le (sq_nonneg r)]
    exact intervalIntegral.intervalIntegral_pos_of_pos hBi hBpos (sq_pos_of_pos hr)
  have hbound (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) (r ^ 2)) :
      eLpNorm (horizontalMollify K (heatSmoothed t f)) p Q ≤ ENNReal.ofReal (B t) := by
    have htm : Measurable (heatSmoothed t f) :=
      (measurable_heatSmoothed_joint hf).comp (measurable_const.prodMk measurable_id)
    calc
      _ ≤ ENNReal.ofReal (∫ z, |K z|) * eLpNorm (heatSmoothed t f) p Q :=
        eLpNorm_horizontalMollify_le hQ hp hpt hK hKi htm
      _ ≤ ENNReal.ofReal A * ENNReal.ofReal (M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hKA) (hheat t ht.1.le)
      _ = ENNReal.ofReal (B t) := by
        rw [← ENNReal.ofReal_mul hA.le]
        congr 1
        dsimp only [B]
        ring
  have h := eLpNorm_setIntegral_le_integral_bound volume measurableSet_Ioc hp hpt
    (measurable_horizontalMollify_heatSmoothed_joint_swap hK hf) hB
    ((intervalIntegrable_iff_integrableOn_Ioc_of_le (sq_nonneg r)).mp hBi) hBpos hmass hbound
  simp only [← intervalIntegral.integral_of_le (sq_nonneg r)] at h
  refine h.trans (ENNReal.ofReal_le_ofReal ?_)
  change (∫ t in (0 : ℝ)..r ^ 2,
    A * M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹)) ≤ 3 * A * M * r
  rw [intervalIntegral.integral_const_mul]
  have htime := integral_heatDecay_le_three_mul hr.le hrR hR
  nlinarith [mul_le_mul_of_nonneg_left htime (mul_pos hA hM).le]

/-- The heat-transfer identity gives the gain of one power of scale in
Step 2 (`paper/main.tex:1033–1041`). Here `s` is the derivative factor `r^k`.
The identity is an explicit internal premise; it is not a literature input. -/
theorem eLpNorm_convolution_le_of_heatTransfer {Q : Measure (FieldPair d)} [SFinite Q]
    (hQ : IsStationary Q) {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {K L : Vec d → ℝ} (hK : Measurable K) (hKi : Integrable K volume)
    (hL : Measurable L) (hLi : Integrable L volume)
    {A B M r R s : ℝ} (hA : 0 < A) (hB : 0 < B) (hM : 0 < M)
    (hr : 0 < r) (hR : 0 < R) (hs : 0 < s) (hrR : r ≤ R)
    (hKA : (∫ z, |K z|) ≤ A * (r ^ 2 / s)) (hLB : (∫ z, |L z|) ≤ B / s)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hheat : ∀ t : ℝ, 0 ≤ t →
      eLpNorm (heatSmoothed t f) p Q ≤
        ENNReal.ofReal (M * ((Real.sqrt (1 + t))⁻¹ + R⁻¹)))
    (htransfer : horizontalMollify K f =ᵐ[Q] fun ω =>
      horizontalMollify K (heatSmoothed (r ^ 2) f) ω -
        ∫ t in (0 : ℝ)..r ^ 2, horizontalMollify L (heatSmoothed t f) ω) :
    eLpNorm (horizontalMollify K f) p Q ≤
      ENNReal.ofReal ((2 * A + 3 * B) * M * (r / s)) := by
  have htm : Measurable (heatSmoothed (r ^ 2) f) :=
    (measurable_heatSmoothed_joint hf).comp (measurable_const.prodMk measurable_id)
  have hboundarym := measurable_horizontalMollify K hK htm
  have htimem : Measurable (fun ω => ∫ t in (0 : ℝ)..r ^ 2,
      horizontalMollify L (heatSmoothed t f) ω) := by
    simp only [intervalIntegral.integral_of_le (sq_nonneg r)]
    exact (measurable_horizontalMollify_heatSmoothed_joint_swap hL hf).stronglyMeasurable
      |>.integral_prod_right'.measurable
  have hdecay : (Real.sqrt (1 + r ^ 2))⁻¹ + R⁻¹ ≤ 2 / r := by
    have hsqrt : r ≤ Real.sqrt (1 + r ^ 2) := Real.le_sqrt_of_sq_le (by linarith)
    have h1 := inv_anti₀ hr hsqrt
    have h2 := inv_anti₀ hr hrR
    calc
      _ ≤ r⁻¹ + r⁻¹ := add_le_add h1 h2
      _ = 2 / r := by ring
  have hboundary : eLpNorm (horizontalMollify K (heatSmoothed (r ^ 2) f)) p Q ≤
      ENNReal.ofReal (2 * A * M * (r / s)) := by
    calc
      _ ≤ ENNReal.ofReal (∫ z, |K z|) * eLpNorm (heatSmoothed (r ^ 2) f) p Q :=
        eLpNorm_horizontalMollify_le hQ hp hpt hK hKi htm
      _ ≤ ENNReal.ofReal (A * (r ^ 2 / s)) *
          ENNReal.ofReal (M * ((Real.sqrt (1 + r ^ 2))⁻¹ + R⁻¹)) :=
        mul_le_mul' (ENNReal.ofReal_le_ofReal hKA) (hheat _ (sq_nonneg r))
      _ = ENNReal.ofReal ((A * (r ^ 2 / s)) *
          (M * ((Real.sqrt (1 + r ^ 2))⁻¹ + R⁻¹))) := by
        exact (ENNReal.ofReal_mul (by positivity : 0 ≤ A * (r ^ 2 / s))).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal (by
        calc
          _ ≤ (A * (r ^ 2 / s)) * (M * (2 / r)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdecay hM.le) (by positivity)
          _ = 2 * A * M * (r / s) := by field_simp)
  have htime := eLpNorm_integral_heatConvolution_le hQ hp hpt hL hLi
    (div_pos hB hs) hM hr hR hrR hLB hf hheat
  rw [eLpNorm_congr_ae htransfer]
  calc
    _ ≤ eLpNorm (horizontalMollify K (heatSmoothed (r ^ 2) f)) p Q +
        eLpNorm (fun ω => ∫ t in (0 : ℝ)..r ^ 2,
          horizontalMollify L (heatSmoothed t f) ω) p Q :=
      eLpNorm_sub_le hboundarym.aestronglyMeasurable htimem.aestronglyMeasurable hp
    _ ≤ ENNReal.ofReal (2 * A * M * (r / s)) + ENNReal.ofReal (3 * (B / s) * M * r) :=
      add_le_add hboundary htime
    _ = _ := by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]
      congr 1
      ring

end EinsteinRelation.Correctors
