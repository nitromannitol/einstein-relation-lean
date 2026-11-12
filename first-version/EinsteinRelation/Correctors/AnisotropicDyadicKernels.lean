import EinsteinRelation.Correctors.RadialDyadicKernels
import EinsteinRelation.Correctors.LinearKernelCalculus

/-! # Compact anisotropic dyadic Poisson kernels

Source: `paper/main.tex:1003–1025`. The inverse square-root change of
coordinates sends the actual radial averaging kernels to normalized
anisotropic kernels and their compact Poisson potentials.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- The averaging kernel after the inverse square-root change of
coordinates (`paper/main.tex:1003–1007`). -/
def anisotropicAverage (B : Vec d ≃L[ℝ] Vec d) (r : ℝ) (x : Vec d) : ℝ :=
  |B.toContinuousLinearMap.det| * radialAverage d r (B x)

/-- Twice the radial Poisson potential, with the determinant normalization
of the inverse square-root change (`paper/main.tex:1009–1018`). -/
def anisotropicBandKernel (B : Vec d ≃L[ℝ] Vec d) (r : ℝ) (x : Vec d) : ℝ :=
  (2 * |B.toContinuousLinearMap.det|) * radialBandKernel d r (B x)

theorem anisotropicAverage_contDiff (B : Vec d ≃L[ℝ] Vec d) {r : ℝ} (hr : 0 < r) :
    ContDiff ℝ (⊤ : ℕ∞) (anisotropicAverage B r) :=
  contDiff_const.mul ((radialAverage_contDiff hr).comp B.contDiff)

theorem anisotropicAverage_hasCompactSupport (B : Vec d ≃L[ℝ] Vec d) {r : ℝ}
    (hr : 0 < r) : HasCompactSupport (anisotropicAverage B r) := by
  exact HasCompactSupport.mul_left (f := fun _ : Vec d => |B.toContinuousLinearMap.det|)
    ((radialAverage_hasCompactSupport hr).comp_homeomorph B.toHomeomorph)

theorem anisotropicAverage_nonneg (B : Vec d ≃L[ℝ] Vec d) {r : ℝ} (hr : 0 < r)
    (x : Vec d) : 0 ≤ anisotropicAverage B r x :=
  mul_nonneg (abs_nonneg _) (radialAverage_nonneg d r hr _)

theorem anisotropicBandKernel_contDiff (hd : 2 ≤ d) (B : Vec d ≃L[ℝ] Vec d)
    {r : ℝ} (hr : 0 < r) : ContDiff ℝ (⊤ : ℕ∞) (anisotropicBandKernel B r) :=
  contDiff_const.mul ((radialBandKernel_contDiff hd hr).comp B.contDiff)

theorem anisotropicBandKernel_hasCompactSupport (hd : 2 ≤ d)
    (B : Vec d ≃L[ℝ] Vec d) {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (anisotropicBandKernel B r) := by
  exact HasCompactSupport.mul_left (f := fun _ : Vec d => 2 * |B.toContinuousLinearMap.det|)
    ((radialBandKernel_hasCompactSupport hd hr).comp_homeomorph B.toHomeomorph)

/-- Euclidean support growth is controlled by the inverse coordinate map
(`paper/main.tex:1010–1018,1079–1084`). -/
theorem anisotropicBandKernel_tail (hd : 2 ≤ d) (B : Vec d ≃L[ℝ] Vec d)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hB : ∀ x, euclideanNorm (B.symm x) ≤ L * euclideanNorm x)
    {x : Vec d} (hx : 2 * L * r ≤ euclideanNorm x) :
    anisotropicBandKernel B r x = 0 := by
  have h := hB (B x)
  rw [B.symm_apply_apply] at h
  have hs : 2 * r ≤ euclideanNorm (B x) := by nlinarith only [h, hx, hL]
  simp only [anisotropicBandKernel, radialBandKernel_tail hd hr hs, mul_zero]

/-- Averaging kernels have the same uniform Euclidean support control
(`paper/main.tex:1003–1007,1079–1084`). -/
theorem anisotropicAverage_tail (B : Vec d ≃L[ℝ] Vec d)
    {L r : ℝ} (hL : 0 < L) (hr : 0 < r)
    (hB : ∀ x, euclideanNorm (B.symm x) ≤ L * euclideanNorm x)
    {x : Vec d} (hx : L * r ≤ euclideanNorm x) : anisotropicAverage B r x = 0 := by
  have h := hB (B x)
  rw [B.symm_apply_apply] at h
  have hs : r ≤ euclideanNorm (B x) := by nlinarith only [h, hx, hL]
  simp only [anisotropicAverage, radialAverage_tail hr hs, mul_zero]

/-- The homogenized coordinate change preserves the exact dyadic scaling
(`paper/main.tex:1015–1018`). -/
theorem anisotropicBandKernel_scaling (hd : 2 ≤ d) (B : Vec d ≃L[ℝ] Vec d)
    {r : ℝ} (hr : 0 < r) :
    anisotropicBandKernel B r = fun x =>
      (r ^ (d - 2))⁻¹ * anisotropicBandKernel B 1 (r⁻¹ • x) := by
  funext x
  have h := radialKernel_scaledProfile hd (g := radialBandProfile d) hr 2 (B x)
  have h1 := radialKernel_scaledProfile hd (g := radialBandProfile d)
    (by norm_num : (0 : ℝ) < 1) 2 (B (r⁻¹ • x))
  simp only [one_pow, inv_one, one_mul, one_smul, map_smul] at h1
  simp only [anisotropicBandKernel, radialBandKernel, h, map_smul, one_mul, h1]
  ring

/-- Every coordinate derivative has an exact scale-independent mass for
a fixed anisotropic coordinate map (`paper/main.tex:1015–1018`). -/
theorem anisotropicBandKernel_derivative_bounds (hd : 2 ≤ d)
    (B : Vec d ≃L[ℝ] Vec d) (cs : List (Fin d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r : ℝ, 0 < r →
      Integrable (coordinateIterate cs (anisotropicBandKernel B r)) volume ∧
      (∫ x : Vec d, |coordinateIterate cs (anisotropicBandKernel B r) x|) =
        C * (r ^ 2 / r ^ cs.length) := by
  refine ⟨∫ x : Vec d, |coordinateIterate cs (anisotropicBandKernel B 1) x|,
    integral_nonneg fun _ => abs_nonneg _, fun r hr => ⟨?_, ?_⟩⟩
  · exact KernelCalculus.integrable_coordinateIterate (anisotropicBandKernel_contDiff hd B hr)
      (anisotropicBandKernel_hasCompactSupport hd B hr) cs
  · rw [anisotropicBandKernel_scaling hd B hr,
      KernelCalculus.integral_abs_coordinateIterate_scaled
        (anisotropicBandKernel_contDiff hd B (by norm_num)) hd hr, mul_comm]

end EinsteinRelation.Correctors
