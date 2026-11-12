import EinsteinRelation.Correctors.AnisotropicDyadicKernels
import EinsteinRelation.Correctors.LinearKernelIntegration

/-! # Normalization of the anisotropic averaging kernels

Source: `paper/main.tex:1003–1007`. The anisotropic averaging kernel has
unit mass in the actual coordinate Lebesgue measure.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- The anisotropic average has integral one (`paper/main.tex:1003–1007`). -/
theorem integral_anisotropicAverage {d : ℕ} (B : Vec d ≃L[ℝ] Vec d)
    {r : ℝ} (hr : 0 < r) : (∫ x, anisotropicAverage B r x) = 1 := by
  unfold anisotropicAverage
  rw [KernelCalculus.integral_normalized_linear, integral_radialAverage hr]

/-- Its `L¹` mass is also one (`paper/main.tex:1028–1042`). -/
theorem integral_abs_anisotropicAverage {d : ℕ} (B : Vec d ≃L[ℝ] Vec d)
    {r : ℝ} (hr : 0 < r) : (∫ x, |anisotropicAverage B r x|) = 1 := by
  simp only [abs_of_nonneg (anisotropicAverage_nonneg B hr _), integral_anisotropicAverage B hr]

end EinsteinRelation.Correctors
