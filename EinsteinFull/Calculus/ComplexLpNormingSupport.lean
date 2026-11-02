import EinsteinFull.Calculus.ComplexTransposeSupport
import Mathlib.MeasureTheory.Function.Holder

open MeasureTheory Filter Set
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull

/-- The pointwise norming test for the complex bilinear Lp pairing. -/
def complexLpNormingTest (p : ℝ) (z : ℂ) : ℂ :=
  (‖z‖ ^ (p - 2)) • star z

/-- Its norm is the conjugate power, including at zero. -/
theorem norm_complexLpNormingTest {p : ℝ} (hp : 1 < p) (z : ℂ) :
    ‖complexLpNormingTest p z‖ = ‖z‖ ^ (p - 1) := by
  by_cases hz : z = 0
  · simp only [complexLpNormingTest, hz, star_zero, smul_zero, norm_zero,
      Real.zero_rpow (by linarith : p - 1 ≠ 0)]
  · have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [complexLpNormingTest, norm_smul, norm_star, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg hr.le _)]
    calc
      _ = ‖z‖ ^ (p - 2) * ‖z‖ ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hr]; congr 1; ring

/-- The actual bilinear product is the positive pth power. -/
theorem mul_complexLpNormingTest {p : ℝ} (hp : 1 < p) (z : ℂ) :
    z * complexLpNormingTest p z = (‖z‖ ^ p : ℝ) := by
  by_cases hz : z = 0
  · simp only [hz, zero_mul, norm_zero, Real.zero_rpow (by linarith : p ≠ 0),
      Complex.ofReal_zero]
  · have hr : 0 < ‖z‖ := norm_pos_iff.mpr hz
    rw [complexLpNormingTest, Complex.real_smul, mul_left_comm, Complex.star_def,
      Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Real.rpow_natCast, ← Real.rpow_add hr]
    congr 2
    ring

/-- The norming test preserves almost-everywhere measurability. -/
theorem aestronglyMeasurable_complexLpNormingTest
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℂ}
    (hf : AEStronglyMeasurable f μ) (p : ℝ) :
    AEStronglyMeasurable (fun x => complexLpNormingTest p (f x)) μ :=
  (hf.norm.aemeasurable.pow_const (p - 2)).aestronglyMeasurable.smul hf.star

/-- The conjugate power moment of the norming test is exactly the original
moment, rather than just bounded by it. -/
theorem norm_complexLpNormingTest_rpow {p q : ℝ}
    (hpq : p.HolderConjugate q) (z : ℂ) :
    ‖complexLpNormingTest p z‖ ^ q = ‖z‖ ^ p := by
  rw [norm_complexLpNormingTest hpq.lt, ← Real.rpow_mul (norm_nonneg z)]
  rw [hpq.sub_one_mul_conj]

/-- Every genuine Lp function supplies its actual Lq norming test. -/
theorem memLp_complexLpNormingTest {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} {p q : ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hpq : p.HolderConjugate q) :
    MemLp (fun x => complexLpNormingTest p (f x)) (ENNReal.ofReal q) μ := by
  apply (integrable_norm_rpow_iff (aestronglyMeasurable_complexLpNormingTest hf.aestronglyMeasurable p)
    (ENNReal.ofReal_pos.mpr hpq.symm.pos).ne' ENNReal.ofReal_ne_top).mp
  simp only [ENNReal.toReal_ofReal hpq.symm.nonneg,
    norm_complexLpNormingTest_rpow hpq]
  simpa only [ENNReal.toReal_ofReal hpq.nonneg] using
    (integrable_norm_rpow_iff hf.aestronglyMeasurable (ENNReal.ofReal_pos.mpr hpq.pos).ne'
      ENNReal.ofReal_ne_top).mpr hf

/-- The real-valued finite Lp norm expressed by its actual power moment. -/
theorem toReal_eLpNorm_eq_root_moment {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℂ} {p : ℝ}
    (hf : MemLp f (ENNReal.ofReal p) μ) (hp : 0 < p) :
    (eLpNorm f (ENNReal.ofReal p) μ).toReal =
      (∫ x, ‖f x‖ ^ p ∂μ) ^ p⁻¹ := by
  rw [hf.eLpNorm_eq_integral_rpow_norm (ENNReal.ofReal_pos.mpr hp).ne'
    ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal hp.le,
    ENNReal.toReal_ofReal (Real.rpow_nonneg
      (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg (f x)) p) _)]

/-- Bilinear duality transfers a genuine high-exponent transpose bound to the
low-exponent forward bound. The norming test is constructed from the actual
output; no norm representation or desired low-exponent estimate is assumed. -/
theorem eLpNorm_le_of_complexL2Transpose_bound
    {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsProbabilityMeasure μ]
    (A : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ) {p q C : ℝ}
    (hpq : p.HolderConjugate q) (hp2 : p ≤ 2) (hq2 : 2 ≤ q) (hC : 0 ≤ C)
    (hB : ∀ (g : Lp ℂ 2 μ), MemLp g (ENNReal.ofReal q) μ →
      eLpNorm (complexL2Transpose μ A g) (ENNReal.ofReal q) μ ≤
        eLpNorm g (ENNReal.ofReal q) μ * ENNReal.ofReal C)
    (f : Lp ℂ 2 μ) :
    eLpNorm (A f) (ENNReal.ofReal p) μ ≤
      eLpNorm f (ENNReal.ofReal p) μ * ENNReal.ofReal C := by
  have hep : ENNReal.ofReal p ≤ 2 := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hp2 : ENNReal.ofReal p ≤ ENNReal.ofReal 2)
  have heq : (2 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hq2 : ENNReal.ofReal 2 ≤ ENNReal.ofReal q)
  have hf := (Lp.memLp f).mono_exponent hep
  have hu := (Lp.memLp (A f)).mono_exponent hep
  let v : α → ℂ := fun x => complexLpNormingTest p (A f x)
  have hvq : MemLp v (ENNReal.ofReal q) μ := memLp_complexLpNormingTest hu hpq
  have hv2 : MemLp v 2 μ := hvq.mono_exponent heq
  let g : Lp ℂ 2 μ := hv2.toLp v
  have hg : (g : α → ℂ) =ᵐ[μ] v := hv2.coeFn_toLp
  have hgq : MemLp g (ENNReal.ofReal q) μ := (memLp_congr_ae hg).mpr hvq
  let M : ℝ := ∫ x, ‖A f x‖ ^ p ∂μ
  have hM : 0 ≤ M := integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _
  have hgm : (∫ x, ‖g x‖ ^ q ∂μ) = M := by
    apply integral_congr_ae
    filter_upwards [hg] with x hx
    rw [hx, norm_complexLpNormingTest_rpow hpq]
  have hpair : (∫ x, A f x * g x ∂μ) = (M : ℂ) := by
    calc
      _ = ∫ x, ((‖A f x‖ ^ p : ℝ) : ℂ) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hg] with x hx
        rw [hx, mul_complexLpNormingTest hpq.lt]
      _ = _ := integral_complex_ofReal
  have hupper : (eLpNorm g (ENNReal.ofReal q) μ * ENNReal.ofReal C) ≠ ⊤ :=
    ENNReal.mul_ne_top hgq.eLpNorm_ne_top ENNReal.ofReal_ne_top
  have hbg := ENNReal.toReal_mono hupper (hB g hgq)
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hC] at hbg
  have hbgmem : MemLp (complexL2Transpose μ A g) (ENNReal.ofReal q) μ :=
    lt_of_le_of_lt (hB g hgq) (lt_top_iff_ne_top.mpr hupper)
  have hholder := (norm_integral_le_integral_norm
    (fun x => f x * complexL2Transpose μ A g x)).trans
    (by simpa only [norm_mul] using integral_mul_norm_le_Lp_mul_Lq hpq hf hbgmem)
  rw [← integral_complexL2Transpose μ A f g, hpair, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hM] at hholder
  have hholder' : M ≤ (eLpNorm f (ENNReal.ofReal p) μ).toReal *
      (eLpNorm (complexL2Transpose μ A g) (ENNReal.ofReal q) μ).toReal := by
    simpa only [toReal_eLpNorm_eq_root_moment hf hpq.pos,
      toReal_eLpNorm_eq_root_moment hbgmem hpq.symm.pos, one_div] using hholder
  have hbound : M ≤ ((eLpNorm f (ENNReal.ofReal p) μ).toReal * C) * M ^ q⁻¹ := by
    apply hholder'.trans
    calc
      _ ≤ (eLpNorm f (ENNReal.ofReal p) μ).toReal *
          ((eLpNorm g (ENNReal.ofReal q) μ).toReal * C) :=
        mul_le_mul_of_nonneg_left hbg ENNReal.toReal_nonneg
      _ = _ := by rw [toReal_eLpNorm_eq_root_moment hgq hpq.symm.pos, hgm]; ring
  have hroot : M ^ p⁻¹ ≤ (eLpNorm f (ENNReal.ofReal p) μ).toReal * C := by
    by_cases hz : M = 0
    · rw [hz, Real.zero_rpow hpq.inv_ne_zero]
      exact mul_nonneg ENNReal.toReal_nonneg hC
    · have hMpos := lt_of_le_of_ne hM (Ne.symm hz)
      have hid : M ^ p⁻¹ * M ^ q⁻¹ = M := by
        rw [← Real.rpow_add hMpos, hpq.inv_add_inv_eq_one, Real.rpow_one]
      exact (mul_le_mul_iff_left₀ (Real.rpow_pos_of_pos hMpos q⁻¹)).mp
        (by simpa only [mul_comm] using hid.le.trans hbound)
  apply (ENNReal.toReal_le_toReal hu.eLpNorm_ne_top
    (ENNReal.mul_ne_top hf.eLpNorm_ne_top ENNReal.ofReal_ne_top)).mp
  rw [toReal_eLpNorm_eq_root_moment hu hpq.pos, ENNReal.toReal_mul,
    ENNReal.toReal_ofReal hC]
  exact hroot

end EinsteinFull
