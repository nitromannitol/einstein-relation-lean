import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Scalar Cauchy--Schwarz in squared integral form. Source:
`paper/main.tex:787–792,850`; integration of the kernel energy. -/
theorem integral_mul_sq_le_integral_sq_mul_integral_sq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {f g : Ω → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x*g x ∂μ)^2 ≤ (∫ x, f x^2 ∂μ)*(∫ x, g x^2 ∂μ) := by
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (ae_of_all μ fun x => abs_nonneg (f x))
    (ae_of_all μ fun x => abs_nonneg (g x))
    (show MemLp (fun x => |f x|) (ENNReal.ofReal 2) μ by simpa using hf.abs)
    (show MemLp (fun x => |g x|) (ENNReal.ofReal 2) μ by simpa using hg.abs)
  have he (v : Ω → ℝ) : (∫ x, |v x|^(2 : ℝ) ∂μ)^(1/(2 : ℝ)) =
      Real.sqrt (∫ x, v x^2 ∂μ) := by
    rw [Real.sqrt_eq_rpow]
    congr 1
    exact integral_congr_ae (ae_of_all μ fun x => by simp only [Real.rpow_two,sq_abs])
  rw [he f,he g] at hh
  have hb : |∫ x, f x*g x ∂μ| ≤
      Real.sqrt (∫ x, f x^2 ∂μ)*Real.sqrt (∫ x, g x^2 ∂μ) := by
    calc
      _ ≤ ∫ x, |f x*g x| ∂μ := abs_integral_le_integral_abs
      _ = ∫ x, |f x| * |g x| ∂μ := integral_congr_ae (ae_of_all μ fun x => abs_mul _ _)
      _ ≤ _ := hh
  have hs := pow_le_pow_left₀ (abs_nonneg _) hb 2
  simpa only [sq_abs,mul_pow,Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (f x)),
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg (g x))] using hs

end EinsteinRelation.Correctors
