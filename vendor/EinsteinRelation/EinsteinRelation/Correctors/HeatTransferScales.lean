import EinsteinRelation.Correctors.HeatSmoothing
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!
# The time integral in the heat-transfer estimates

The last inequality of Proposition 6.1, Step 2 (`paper/main.tex:1023–1031`),
uses the integral of `(1+t)^{-1/2} + R^{-1}` up to `r²`. This file computes
that integral and proves explicit bounds uniform in `1 ≤ r ≤ R`.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

/-- The decay profile in the scalar averaging assumption
(`paper/main.tex:962–964`). -/
def heatAveragingProfile (R t : ℝ) : ℝ := (Real.sqrt (1 + t))⁻¹ + R⁻¹

/-- The time profile is nonnegative for positive outer scale. -/
theorem heatAveragingProfile_nonneg {R : ℝ} (hR : 0 < R) (t : ℝ) :
    0 ≤ heatAveragingProfile R t :=
  add_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) (inv_nonneg.mpr hR.le)

/-- The averaging profile is continuous at every nonnegative time. -/
theorem continuousOn_heatAveragingProfile (R : ℝ) :
    ContinuousOn (heatAveragingProfile R) (Set.Ici 0) := by
  apply ContinuousOn.add _ continuousOn_const
  apply ContinuousOn.inv₀ ((continuous_const.add continuous_id).sqrt.continuousOn)
  intro t ht
  change Real.sqrt (1 + t) ≠ 0
  exact (Real.sqrt_pos.mpr (by linarith [show 0 ≤ t from ht])).ne'

/-- Integrability of the averaging profile over any finite positive time interval. -/
theorem intervalIntegrable_heatAveragingProfile (R : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    IntervalIntegrable (heatAveragingProfile R) volume 0 T := by
  exact ((continuousOn_heatAveragingProfile R).mono
    (fun _ ht => ht.1)).intervalIntegrable_of_Icc hT

/-- Exact integral of the averaging profile (`paper/main.tex:1025–1026`). -/
theorem integral_heatAveragingProfile (R : ℝ) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in (0 : ℝ)..T, heatAveragingProfile R t) =
      2 * (Real.sqrt (1 + T) - 1) + T * R⁻¹ := by
  have hderiv : ∀ t ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun s => 2 * (Real.sqrt (1 + s) - 1) + s * R⁻¹)
        (heatAveragingProfile R t) t := by
    intro t ht
    have hpos : 0 < 1 + t := by linarith [ht.1]
    have hsq : 0 < Real.sqrt (1 + t) := Real.sqrt_pos.mpr hpos
    have h1 : HasDerivAt (fun s : ℝ => 1 + s) 1 t := (hasDerivAt_id t).const_add 1
    have h2 : HasDerivAt (fun s : ℝ => Real.sqrt (1 + s)) (1 / (2 * Real.sqrt (1 + t))) t :=
      h1.sqrt hpos.ne'
    have h3 : HasDerivAt (fun s : ℝ => 2 * (Real.sqrt (1 + s) - 1) + s * R⁻¹)
        (2 * (1 / (2 * Real.sqrt (1 + t))) + 1 * R⁻¹) t :=
      ((h2.sub_const 1).const_mul 2).add ((hasDerivAt_id t).mul_const R⁻¹)
    refine h3.congr_deriv ?_
    unfold heatAveragingProfile
    field_simp <;> ring
  have hcont : ContinuousOn (fun s => 2 * (Real.sqrt (1 + s) - 1) + s * R⁻¹)
      (Set.Icc 0 T) := by fun_prop
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hT hcont hderiv
    (intervalIntegrable_heatAveragingProfile R hT)
  simpa only [add_zero, Real.sqrt_one, sub_self, mul_zero, zero_mul, zero_add, sub_zero] using h

/-- At the band time `r²`, the averaging profile is at most `2/r` for `0 < r ≤ R`. -/
theorem heatAveragingProfile_sq_le {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    heatAveragingProfile R (r ^ 2) ≤ 2 * r⁻¹ := by
  have hs : r ≤ Real.sqrt (1 + r ^ 2) :=
    (Real.le_sqrt hr.le (by positivity)).mpr (by linarith)
  have h₁ : (Real.sqrt (1 + r ^ 2))⁻¹ ≤ r⁻¹ := inv_anti₀ hr hs
  have h₂ : R⁻¹ ≤ r⁻¹ := inv_anti₀ hr hrR
  dsimp [heatAveragingProfile]
  linarith

/-- Integrating the profile up to `r²` costs at most `3r`, uniformly for `0 < r ≤ R`
(`paper/main.tex:1025–1026`). -/
theorem integral_heatAveragingProfile_sq_le {r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) :
    (∫ t in (0 : ℝ)..r ^ 2, heatAveragingProfile R t) ≤ 3 * r := by
  rw [integral_heatAveragingProfile R (sq_nonneg r)]
  have hs : Real.sqrt (1 + r ^ 2) ≤ r + 1 :=
    (Real.sqrt_le_iff).mpr ⟨by linarith, by nlinarith⟩
  have hR : 0 < R := hr.trans_le hrR
  have hmul : r ^ 2 * R⁻¹ ≤ r := by
    rw [mul_inv_le_iff₀ hR]
    nlinarith [mul_le_mul_of_nonneg_left hrR hr.le]
  linarith

/-- Explicit scale arithmetic for the band and remainder estimates in
`paper/main.tex:1023–1031`. If the kernel mass is at most `A r² s` and its
Laplacian mass is at most `B s`, the heat-transfer bound is at most
`(2A+3B) M r s`. Taking `s = 1, r⁻¹, r⁻²` gives the three band orders;
taking `r = R` and `s = R⁻²` gives the remainder order. -/
theorem heat_transfer_scale_bound {r R M A B s a b : ℝ}
    (hr : 0 < r) (hrR : r ≤ R) (hM : 0 ≤ M) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hs : 0 ≤ s)
    (ha_bound : a ≤ A * r ^ 2 * s) (hb_bound : b ≤ B * s) :
    a * M * heatAveragingProfile R (r ^ 2) +
        b * M * (∫ t in (0 : ℝ)..r ^ 2, heatAveragingProfile R t) ≤
      (2 * A + 3 * B) * M * r * s := by
  have h₁ := heatAveragingProfile_sq_le hr hrR
  have h₂ := integral_heatAveragingProfile_sq_le hr hrR
  have hR : 0 < R := hr.trans_le hrR
  have hI : 0 ≤ ∫ t in (0 : ℝ)..r ^ 2, heatAveragingProfile R t :=
    intervalIntegral.integral_nonneg (sq_nonneg r) fun t _ =>
      heatAveragingProfile_nonneg hR t
  calc
    _ ≤ (A * r ^ 2 * s) * M * (2 * r⁻¹) + (B * s) * M * (3 * r) := by
      apply add_le_add
      · exact mul_le_mul (mul_le_mul_of_nonneg_right ha_bound hM) h₁
          (heatAveragingProfile_nonneg hR _) (by positivity)
      · exact mul_le_mul (mul_le_mul_of_nonneg_right hb_bound hM) h₂ hI (by positivity)
    _ = _ := by field_simp

end EinsteinRelation.Correctors
