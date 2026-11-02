import EinsteinRelation.Correctors.BallMeanSquareScaling
import Mathlib.MeasureTheory.Function.L2Space

/-! # Comparing centered means on nested Euclidean balls

Source: `paper/main.tex:693-698,798-806`. Expanding the square around an
arbitrary constant proves the mean-square inequality, and the exact ball
volume ratio controls successive dyadic means.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- Expansion of a square about a constant under a finite nonzero average. -/
theorem average_sq_sub_const {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ.real Set.univ ≠ 0)
    {u : X → ℝ} (hu : MemLp u 2 μ) (c : ℝ) :
    (⨍ x, (u x-c)^2 ∂μ) = (⨍ x, u x^2 ∂μ) - 2*c*(⨍ x, u x ∂μ) + c^2 := by
  have hi := hu.integrable one_le_two
  have he : (fun x => (u x-c)^2) = fun x => u x^2 - (2*c)*u x + c^2 := by
    funext x
    ring
  rw [he]
  simp only [average_eq, smul_eq_mul]
  have ha := integral_add (hu.integrable_sq.sub (hi.const_mul (2*c)))
    (integrable_const (c^2) : Integrable (fun _ : X => c^2) μ)
  have hs := integral_sub hu.integrable_sq (hi.const_mul (2*c))
  simp only [Pi.sub_apply] at ha hs
  rw [ha, hs, integral_const_mul, integral_const]
  simp only [smul_eq_mul]
  field_simp [hμ]


/-- The square of the average is bounded by the average square. -/
theorem sq_average_le_average_sq {X : Type*} [MeasurableSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (hμ : μ.real Set.univ ≠ 0)
    {u : X → ℝ} (hu : MemLp u 2 μ) :
    (⨍ x, u x ∂μ)^2 ≤ (⨍ x, u x^2 ∂μ) := by
  have hn : 0 ≤ (⨍ x, (u x - ⨍ y, u y ∂μ)^2 ∂μ) :=
    integral_nonneg fun _ => sq_nonneg _
  rw [average_sq_sub_const μ hμ hu] at hn
  nlinarith

/-- Centered and constant parts bound the actual uncentered mean square. -/
theorem average_sq_le_twice_centered_add_mean {d : ℕ} (u : Vec d → ℝ)
    (R : ℝ) (hR : 0 < R) (hu : MemLp u 2 (volume.restrict (ball 0 R))) :
    (⨍ x in ball 0 R, u x^2) ≤
      2*(⨍ x in ball 0 R, (u x-⨍ y in ball 0 R, u y)^2) +
        2*(⨍ x in ball 0 R, u x)^2 := by
  have hp := ball_volume_pos_finite d R hR
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp hp).2.ne
  have hm : (volume.restrict (ball (0 : Vec d) R)).real Set.univ ≠ 0 := by
    simpa only [measureReal_restrict_apply_univ] using hp.ne'
  have he := average_sq_sub_const (volume.restrict (ball (0 : Vec d) R)) hm hu
    (⨍ y in ball 0 R, u y)
  have hn : 0 ≤ (⨍ x in ball (0 : Vec d) R, (u x-⨍ y in ball 0 R, u y)^2) :=
    integral_nonneg fun _ => sq_nonneg _
  nlinarith [sq_nonneg (⨍ x in ball (0 : Vec d) R, u x)]

/-- The change of means is bounded by the centered square on the doubled ball. -/
theorem sq_ball_mean_sub_double_mean_le {d : ℕ} (u : Vec d → ℝ)
    (R : ℝ) (hR : 0 < R)
    (hu : MemLp u 2 (volume.restrict (ball 0 (2*R)))) :
    ((⨍ x in ball 0 R, u x) - (⨍ x in ball 0 (2*R), u x))^2 ≤
      (2:ℝ)^d * (⨍ x in ball 0 (2*R), (u x-⨍ y in ball 0 (2*R), u y)^2) := by
  have hsmall : ball (0 : Vec d) R ⊆ ball 0 (2*R) := by
    intro x hx
    change euclideanNorm (x-0) < 2*R
    exact lt_of_lt_of_le hx (by linarith)
  have hp := ball_volume_pos_finite d R hR
  have hp2 := ball_volume_pos_finite d (2*R) (by positivity)
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) R)) :=
    isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp hp).2.ne
  haveI : IsFiniteMeasure (volume.restrict (ball (0 : Vec d) (2*R))) :=
    isFiniteMeasure_restrict.mpr (ENNReal.toReal_pos_iff.mp hp2).2.ne
  have hm : (volume.restrict (ball (0 : Vec d) R)).real Set.univ ≠ 0 := by
    simpa only [measureReal_restrict_apply_univ] using hp.ne'
  have hus := hu.mono_measure (Measure.restrict_mono hsmall le_rfl)
  have hj := sq_average_le_average_sq (volume.restrict (ball (0 : Vec d) R)) hm hus
  let c : ℝ := ⨍ x in ball 0 (2*R), u x
  have he := average_sq_sub_const (volume.restrict (ball (0 : Vec d) R)) hm hus c
  have hfirst : ((⨍ x in ball 0 R, u x)-c)^2 ≤
      (⨍ x in ball 0 R, (u x-c)^2) := by nlinarith only [he, hj]
  have hc : MemLp (fun x => u x-c) 2 (volume.restrict (ball 0 (2*R))) :=
    hu.sub (memLp_const c)
  have hi : (∫ x in ball (0 : Vec d) R, (u x-c)^2) ≤
      ∫ x in ball (0 : Vec d) (2*R), (u x-c)^2 :=
    setIntegral_mono_set hc.integrable_sq (Filter.Eventually.of_forall fun _ => sq_nonneg _)
      (Filter.Eventually.of_forall fun _ hx => hsmall hx)
  have hv : volume.real (ball (0 : Vec d) (2*R)) =
      (2:ℝ)^d * volume.real (ball (0 : Vec d) R) := by
    rw [volume_real_euclideanBall (2*R) (by positivity), volume_real_euclideanBall R hR,
      mul_pow, mul_assoc]
  apply hfirst.trans
  change (⨍ x in ball 0 R, (u x-c)^2) ≤
    (2:ℝ)^d * (⨍ x in ball 0 (2*R), (u x-c)^2)
  simp only [setAverage_eq, smul_eq_mul]
  rw [hv, mul_inv]
  calc
    _ ≤ (volume.real (ball (0 : Vec d) R))⁻¹ *
        ∫ x in ball (0 : Vec d) (2*R), (u x-c)^2 :=
      mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr hp.le)
    _ = _ := by field_simp [hp.ne', pow_ne_zero d (by norm_num : (2:ℝ) ≠ 0)]

end EinsteinRelation.Correctors
