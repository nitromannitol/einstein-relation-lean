import EinsteinRelation.Correctors.SpatialBallVolume
import EinsteinRelation.Correctors.AKMSublinearOscillation
import Mathlib.MeasureTheory.Function.L2Space

/-! # Subtraction of centered sublinear oscillations

Source: `paper/main.tex:693-698,727-729`. The centered second moment of
a difference is bounded by twice the sum of the two centered moments.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The elementary square inequality for centered L² functions. -/
theorem average_centered_sub_sq_le {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (u v : A → ℝ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    (⨍ x, ((u x - v x) - ⨍ y, u y - v y ∂μ)^2 ∂μ) ≤
      2 * (⨍ x, (u x - ⨍ y, u y ∂μ)^2 ∂μ) +
      2 * (⨍ x, (v x - ⨍ y, v y ∂μ)^2 ∂μ) := by
  have hmean : (⨍ y, u y - v y ∂μ) = (⨍ y, u y ∂μ) - ⨍ y, v y ∂μ :=
    integral_sub (hu.integrable (by norm_num)).to_average
      (hv.integrable (by norm_num)).to_average
  have hiu : Integrable (fun x => (u x - ⨍ y, u y ∂μ)^2) μ := (hu.sub (memLp_const (⨍ y, u y ∂μ))).integrable_sq
  have hiv : Integrable (fun x => (v x - ⨍ y, v y ∂μ)^2) μ := (hv.sub (memLp_const (⨍ y, v y ∂μ))).integrable_sq
  have hid : Integrable (fun x => ((u x-v x) - ⨍ y, u y-v y ∂μ)^2) μ := ((hu.sub hv).sub (memLp_const (⨍ y, u y - v y ∂μ))).integrable_sq
  calc
    _ ≤ (⨍ x, 2 * (u x - ⨍ y, u y ∂μ)^2 +
        2 * (v x - ⨍ y, v y ∂μ)^2 ∂μ) := by
      apply integral_mono hid.to_average ((hiu.const_mul 2).add (hiv.const_mul 2)).to_average
      intro x
      dsimp only [Pi.sub_apply, Pi.add_apply]
      rw [hmean]
      nlinarith only [sq_nonneg ((u x - (⨍ y, u y ∂μ)) +
        (v x - (⨍ y, v y ∂μ)))]
    _ = _ := by
      change (∫ x, 2 * _ + 2 * _ ∂(μ Set.univ)⁻¹ • μ) = _
      rw [integral_add (hiu.const_mul 2).to_average (hiv.const_mul 2).to_average,
        integral_const_mul, integral_const_mul]
      rfl

/-- Centered L² sublinearity is stable under subtraction. -/
theorem sublinear_centered_oscillation_sub {d : ℕ} (u v : Vec d → ℝ)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (hv : ∀ R : ℝ, 0 < R → MemLp v 2 (volume.restrict (ball 0 R)))
    (hsubu : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (u x - ⨍ y in ball 0 R, u y ∂volume)^2 ∂volume)) atTop (𝓝 0))
    (hsubv : Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      (v x - ⨍ y in ball 0 R, v y ∂volume)^2 ∂volume)) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
      ((u x-v x) - ⨍ y in ball 0 R, u y-v y ∂volume)^2 ∂volume)) atTop (𝓝 0) := by
  have htop := (hsubu.add hsubv).const_mul (Real.sqrt 2)
  simp only [add_zero, mul_zero] at htop
  apply squeeze_zero' _ _ htop
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact mul_nonneg (inv_nonneg.mpr hR.le) (Real.sqrt_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    let μ := volume.restrict (ball (0 : Vec d) R)
    letI : IsFiniteMeasure μ := ⟨by
      simpa [μ] using (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d R hR)).2⟩
    have hb := average_centered_sub_sq_le μ u v (hu R hR) (hv R hR)
    have hs := Real.sqrt_le_sqrt hb
    have hn₁ : 0 ≤ (⨍ x, (u x - ⨍ y, u y ∂μ)^2 ∂μ) :=
      integral_nonneg fun _ => sq_nonneg _
    have hn₂ : 0 ≤ (⨍ x, (v x - ⨍ y, v y ∂μ)^2 ∂μ) :=
      integral_nonneg fun _ => sq_nonneg _
    have hs' : Real.sqrt (⨍ x, ((u x-v x) - ⨍ y, u y-v y ∂μ)^2 ∂μ) ≤
        Real.sqrt 2 * ((Real.sqrt (⨍ x, (u x - ⨍ y, u y ∂μ)^2 ∂μ)) +
          Real.sqrt (⨍ x, (v x - ⨍ y, v y ∂μ)^2 ∂μ)) := by
      calc
        _ ≤ Real.sqrt (2 * ((⨍ x, (u x - ⨍ y, u y ∂μ)^2 ∂μ) +
            (⨍ x, (v x - ⨍ y, v y ∂μ)^2 ∂μ))) := by
          simpa only [mul_add] using hs
        _ ≤ _ := by
          rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
          apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg 2)
          apply Real.sqrt_le_iff.mpr
          refine ⟨add_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _), ?_⟩
          nlinarith only [Real.sq_sqrt hn₁, Real.sq_sqrt hn₂,
            mul_nonneg (Real.sqrt_nonneg (⨍ x, (u x - ⨍ y, u y ∂μ)^2 ∂μ))
              (Real.sqrt_nonneg (⨍ x, (v x - ⨍ y, v y ∂μ)^2 ∂μ))]
    have hmul := mul_le_mul_of_nonneg_left hs' (inv_nonneg.mpr hR.le)
    convert hmul using 1; dsimp only [μ]; ring

end EinsteinRelation.Correctors
