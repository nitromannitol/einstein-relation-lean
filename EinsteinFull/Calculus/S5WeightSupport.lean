import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.MeasureTheory.Function.LpSeminorm.Monotonicity
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Multiplication by a bounded real weight on complex `L²`

The weighted Davies estimate is run on the bounded multiplication operator
`f ↦ w • f`, which is a bounded complex linear map of `Lp ℂ 2 μ`.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section
namespace EinsteinFull

section S5Weight

variable {α : Type*} [MeasurableSpace α]

theorem s5_memLp_mul {μ : Measure α} {w : α → ℝ} (hw : Measurable w) {B : ℝ}
    (hB : ∀ x, |w x| ≤ B) (f : Lp ℂ 2 μ) : MemLp (fun x => (w x : ℂ) * f x) 2 μ := by
  refine (Lp.memLp f).of_le_mul (c := B) ?_ (Filter.Eventually.of_forall fun x => ?_)
  · exact (Complex.measurable_ofReal.comp hw).aestronglyMeasurable.mul
      (Lp.aestronglyMeasurable f)
  · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)

private def s5MulLp (μ : Measure α) {w : α → ℝ} (hw : Measurable w) {B : ℝ}
    (hB : ∀ x, |w x| ≤ B) (f : Lp ℂ 2 μ) : Lp ℂ 2 μ :=
  (s5_memLp_mul hw hB f).toLp _

private theorem s5MulLp_coe (μ : Measure α) {w : α → ℝ} (hw : Measurable w) {B : ℝ}
    (hB : ∀ x, |w x| ≤ B) (f : Lp ℂ 2 μ) :
    (s5MulLp μ hw hB f : α → ℂ) =ᵐ[μ] fun x => (w x : ℂ) * f x :=
  MemLp.coeFn_toLp _

private def s5MulLinear (μ : Measure α) {w : α → ℝ} (hw : Measurable w) {B : ℝ}
    (hB : ∀ x, |w x| ≤ B) : Lp ℂ 2 μ →ₗ[ℂ] Lp ℂ 2 μ where
  toFun := s5MulLp μ hw hB
  map_add' f g := by
    apply Lp.ext
    filter_upwards [s5MulLp_coe μ hw hB (f + g), s5MulLp_coe μ hw hB f,
      s5MulLp_coe μ hw hB g, Lp.coeFn_add (s5MulLp μ hw hB f) (s5MulLp μ hw hB g),
      Lp.coeFn_add f g] with x hsum hf hg hout hin
    rw [hsum, hout]
    simp only [Pi.add_apply]
    rw [hf, hg]
    simp only [hin, Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    filter_upwards [s5MulLp_coe μ hw hB (c • f), s5MulLp_coe μ hw hB f,
      Lp.coeFn_smul c (s5MulLp μ hw hB f), Lp.coeFn_smul c f] with x hcf hf hout hin
    simp only [RingHom.id_apply]
    rw [hcf, hout]
    simp only [Pi.smul_apply]
    rw [hf]
    simp only [hin, Pi.smul_apply, smul_eq_mul]
    ring

/-- Multiplication by the bounded measurable real weight `w` on complex `L²(μ)`. -/
def s5Mul (μ : Measure α) {w : α → ℝ} (hw : Measurable w) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |w x| ≤ B) : Lp ℂ 2 μ →L[ℂ] Lp ℂ 2 μ :=
  LinearMap.mkContinuous (s5MulLinear μ hw hB) B (fun f => by
    change ‖(s5_memLp_mul hw hB f).toLp _‖ ≤ B * ‖f‖
    rw [Lp.norm_toLp, Lp.norm_def]
    have h := eLpNorm_le_mul_eLpNorm_of_ae_le_mul (μ := μ)
      (f := fun x => (w x : ℂ) * f x) (g := (f : α → ℂ)) (c := B)
      ((Complex.measurable_ofReal.comp hw).aestronglyMeasurable.mul
        (Lp.aestronglyMeasurable f))
      (Filter.Eventually.of_forall fun x => by
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_right (hB x) (norm_nonneg _)) 2
    calc (eLpNorm (fun x => (w x : ℂ) * f x) 2 μ).toReal
        ≤ (ENNReal.ofReal B * eLpNorm (f : α → ℂ) 2 μ).toReal :=
          ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (Lp.eLpNorm_ne_top f)) h
      _ = B * (eLpNorm (f : α → ℂ) 2 μ).toReal := by
          rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hB0])

theorem s5Mul_coe (μ : Measure α) {w : α → ℝ} (hw : Measurable w) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |w x| ≤ B) (f : Lp ℂ 2 μ) :
    (s5Mul μ hw hB0 hB f : α → ℂ) =ᵐ[μ] fun x => (w x : ℂ) * f x :=
  s5MulLp_coe μ hw hB f

theorem s5Mul_norm (μ : Measure α) {w : α → ℝ} (hw : Measurable w) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x, |w x| ≤ B) (f : Lp ℂ 2 μ) :
    ‖s5Mul μ hw hB0 hB f‖ = (eLpNorm (fun x => (w x : ℂ) * f x) 2 μ).toReal := by
  change ‖(s5_memLp_mul hw hB f).toLp _‖ = _
  rw [Lp.norm_toLp]

end S5Weight

end EinsteinFull
