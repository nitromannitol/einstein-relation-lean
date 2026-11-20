import EinsteinFull.External.DFGW.RealBrownian
import Mathlib.Probability.Distributions.Gaussian.HasGaussianLaw.Basic

/-! # Characteristic functions of real Brownian motion

Finite linear combinations of a real Brownian process are centered Gaussians with covariance
obtained by summing the two-time covariances.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- The characteristic function of a finite linear combination of real Brownian coordinates. -/
theorem isPreBrownianReal_integral_exp_sum (hB : IsPreBrownianReal B P)
    (n : ℕ) (t : Fin n → ℝ≥0) (a : Fin n → ℝ) :
    (∫ ω, Complex.exp (Complex.I * ((∑ k, a k * B (t k) ω) : ℂ)) ∂P) =
      Complex.exp (((-(1 / 2 : ℝ)) * ∑ k, ∑ l,
        (min (t k) (t l) : ℝ) * a k * a l) : ℂ) := by
  let : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  let Z : Fin n → Ω → ℝ := fun k ω => a k * B (t k) ω
  have hZ (k : Fin n) : MemLp (Z k) 2 P := by
    exact ((hB.isGaussianProcess.hasGaussianLaw_eval (t k)).memLp_two).const_mul (a k)
  have hgauss : HasGaussianLaw (fun ω => ∑ k, Z k ω) P := by
    have h := ((hB.isGaussianProcess.comp_right t).smul a).hasGaussianLaw_fun_sum
      (I := Finset.univ)
    simpa only [smul_eq_mul, Function.comp_apply, Z] using h
  have hmean : (∫ ω, ∑ k, Z k ω ∂P) = 0 := by
    rw [integral_finsetSum _ (fun k _ => (hZ k).integrable (by norm_num))]
    simp only [Z, integral_const_mul, hB.integral_eval, mul_zero, Finset.sum_const_zero]
  have hvar : Var[fun ω => ∑ k, Z k ω; P] = ∑ k, ∑ l,
      (min (t k) (t l) : ℝ) * a k * a l := by
    rw [variance_fun_sum hZ]
    apply Finset.sum_congr rfl
    intro k _
    apply Finset.sum_congr rfl
    intro l _
    change cov[a k • B (t k), a l • B (t l); P] = _
    rw [covariance_smul_left, covariance_smul_right, hB.covariance_eval, NNReal.coe_min]
    ring
  have hchar := hgauss.charFun_map_eq (1 : ℝ)
  rw [charFun_apply_real, integral_map hgauss.aemeasurable (by fun_prop)] at hchar
  simp only [Complex.ofReal_one, one_mul, RCLike.inner_apply, conj_trivial, mul_one,
    hmean, Complex.ofReal_zero, zero_mul, zero_sub, hvar] at hchar
  have hleft : (∫ ω, Complex.exp (Complex.I * ((∑ k, a k * B (t k) ω) : ℂ)) ∂P) =
      ∫ ω, Complex.exp (((∑ k, Z k ω : ℝ) : ℂ) * Complex.I) ∂P := by
    apply integral_congr_ae
    filter_upwards with ω
    simp only [Z, mul_comm Complex.I, Complex.ofReal_sum, Complex.ofReal_mul]
  rw [hleft, hchar]
  congr 1
  push_cast
  ring

end EinsteinFull.External.DFGW
