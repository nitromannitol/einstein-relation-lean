import EinsteinFull.Frozen.GaussianTestControl
import EinsteinFull.Calculus.C3FluxGeneralTestTransfer
import EinsteinFull.Calculus.CarverSFluxGaussianGain
import EinsteinFull.Calculus.SchwartzAverageSupport
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Pi
import EinsteinFull.Work.W3.GaussianSchwartzBoundsSupport
import Mathlib.LinearAlgebra.Matrix.AbsoluteValue

/-! Estimates for the actual Gaussian-controlled Schwartz tests used in the
forced-flux gain. All spatial integrals use the original coordinate carrier
with its product Lebesgue measure and the explicit Euclidean norm. -/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

private lemma flux_test_gaussian_product (d : ℕ) (b : ℝ) (x : Vec d) :
    Real.exp (-b * euclideanNorm x ^ 2) =
      ∏ i : Fin d, Real.exp (-b * (x i) ^ 2) := by
  have hsq : euclideanNorm x ^ 2 = ∑ i : Fin d, (x i) ^ 2 := by
    unfold euclideanNorm euclideanSq dot
    rw [Real.sq_sqrt (Finset.sum_nonneg (fun i _ => mul_self_nonneg (x i)))]
    simp only [pow_two]
  rw [hsq, Finset.mul_sum, Real.exp_sum]

private lemma flux_test_gaussian_integrable (d : ℕ) (b : ℝ) (hb : 0 < b) :
    Integrable (fun x : Vec d => Real.exp (-b * euclideanNorm x ^ 2)) volume := by
  simp_rw [flux_test_gaussian_product]
  exact Integrable.fintype_prod_dep (fun _ => integrable_exp_neg_mul_sq hb)

private lemma flux_test_gaussian_integral (d : ℕ) (b : ℝ) :
    (∫ x : Vec d, Real.exp (-b * euclideanNorm x ^ 2)) =
      Real.sqrt (Real.pi / b) ^ d := by
  simp_rw [flux_test_gaussian_product]
  calc
    _ = (∫ y : ℝ, Real.exp (-b * y ^ 2)) ^ d := by
      simpa only [Fintype.card_fin] using
        (integral_fintype_prod_volume_eq_pow (ι := Fin d)
          (fun y : ℝ => Real.exp (-b * y ^ 2)))
    _ = _ := congrArg (fun a : ℝ => a ^ d) (integral_gaussian b)

/-- The zeroth Gaussian test envelope gives a scale-uniform L1 estimate, with
the constant chosen before the scale, derivative order, and test. -/
theorem carverS_gaussian_test_L1_bound (d : ℕ) (ctest : ℝ) (hctest : 0 < ctest)
    (Btest : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ), 1 ≤ s → ∀ (k : ℕ)
      (ψ : SchwartzMap (Vec d) ℂ), HasGaussianTestControl s k ctest Btest ψ →
      Integrable (fun x => ψ x) (volume : Measure (Vec d)) ∧
      (∫ x : Vec d, ‖ψ x‖ ∂volume) ≤ C * Btest 0 * s ^ (-(k : ℝ) / 2) := by
  refine ⟨Real.sqrt (Real.pi / ctest) ^ d, by positivity, ?_⟩
  intro s hs k ψ hψ
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have henv (x : Vec d) : ‖ψ x‖ ≤
      Btest 0 * s ^ (-(d : ℝ) / 2 - (k : ℝ) / 2) *
        Real.exp (-(ctest / s) * euclideanNorm x ^ 2) := by
    have h := hψ 0 (fun i => Fin.elim0 i) x
    rw [show -(ctest / s) * euclideanNorm x ^ 2 =
      -ctest * euclideanNorm x ^ 2 / s by ring]
    simpa only [iteratedFDeriv_zero_apply, Nat.zero_add] using h
  refine ⟨ψ.integrable, ?_⟩
  have hle := integral_mono ψ.integrable.norm
    ((flux_test_gaussian_integrable d (ctest / s) (div_pos hctest hs0)).const_mul
      (Btest 0 * s ^ (-(d : ℝ) / 2 - (k : ℝ) / 2))) henv
  rw [integral_const_mul, flux_test_gaussian_integral] at hle
  have hscale : Real.sqrt (Real.pi / (ctest / s)) ^ d =
      Real.sqrt (Real.pi / ctest) ^ d * s ^ ((d : ℝ) / 2) := by
    rw [div_div_eq_mul_div]
    have heq : Real.pi * s / ctest = (Real.pi / ctest) * s := by ring
    rw [heq, Real.sqrt_mul (div_nonneg Real.pi_pos.le hctest.le), mul_pow,
      Real.sqrt_eq_rpow s, ← Real.rpow_natCast (s ^ (1 / (2 : ℝ))) d,
      ← Real.rpow_mul hs0.le]
    congr 2
    ring
  rw [hscale] at hle
  convert hle using 1
  rw [show Btest 0 * s ^ (-(d : ℝ) / 2 - (k : ℝ) / 2) *
      (Real.sqrt (Real.pi / ctest) ^ d * s ^ ((d : ℝ) / 2)) =
      Real.sqrt (Real.pi / ctest) ^ d * Btest 0 *
        (s ^ (-(d : ℝ) / 2 - (k : ℝ) / 2) * s ^ ((d : ℝ) / 2)) by ring,
    ← Real.rpow_add hs0]
  congr 2
  ring

/-- The test-mass estimate acts on the literal stationary averaging operator,
with a constant independent of the environment law and the averaged field. -/
theorem carverS_gaussian_test_stationaryAverage_L2_bound (d : ℕ) (ctest : ℝ)
    (hctest : 0 < ctest) (Btest : ℕ → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (s : ℝ), 1 ≤ s → ∀ (k : ℕ)
      (ψ : SchwartzMap (Vec d) ℂ), HasGaussianTestControl s k ctest Btest ψ →
      ∀ {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (F : Lp ℂ 2 (reducedLaw Q)),
        ‖stationarySchwartzAverage Q ψ F‖ ≤
          C * Btest 0 * s ^ (-(k : ℝ) / 2) * ‖F‖ := by
  obtain ⟨C, hC, hmass⟩ := carverS_gaussian_test_L1_bound d ctest hctest Btest
  refine ⟨C, hC, ?_⟩
  intro s hs k ψ hψ Λ₀ r₀ Q F
  calc
    _ ≤ ∫ y : Vec d, ‖ψ (-y) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y F‖ :=
      norm_integral_le_integral_norm _
    _ = (∫ y : Vec d, ‖ψ y‖) * ‖F‖ := by
      simp_rw [norm_smul, LinearIsometry.norm_map]
      rw [integral_mul_const, integral_neg_eq_self (fun y : Vec d => ‖ψ y‖) volume]
    _ ≤ _ := mul_le_mul_of_nonneg_right (hmass s hs k ψ hψ).2 (norm_nonneg F)

/-- The same physical partition reconstructs the centered stationary average
for every Schwartz test, without selecting new endpoint fields. -/
lemma flux_schwartz_centered_partition_hasSum {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {r : ℝ} (hr : 0 < r)
    (ψ : SchwartzMap (Vec d) ℂ) (F : Lp ℂ 2 (reducedLaw Q)) :
    HasSum (fun z : Fin d → ℤ => centeredComplexLp Q (∫ y : Vec d,
      ((fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) : ℂ) * ψ (-y)) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y F))
      (stationarySchwartzAverage Q ψ (centeredComplexLp Q F)) := by
  letI := reducedLaw_probability Q
  let f := fun y : Vec d => ψ (-y) •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y F
  have hf : Integrable f := integrable_stationarySchwartzAverage_integrand Q ψ F
  have hsum := (centeredComplexLpCLM Q).hasSum (flux_partition_integral_hasSum hr f hf)
  have he : centeredComplexLpCLM Q (∫ y, f y) =
      stationarySchwartzAverage Q ψ (centeredComplexLp Q F) := by
    rw [← (centeredComplexLpCLM Q).integral_comp_comm hf]
    unfold stationarySchwartzAverage
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun y => by
      simp only [f, map_smul, centeredComplexLpCLM_apply, flux_centered_complexTranslation]
  rw [he] at hsum
  convert hsum using 1
  funext z
  rw [centeredComplexLpCLM_apply]
  apply congrArg (centeredComplexLp Q)
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [f, ← smul_assoc, Complex.real_smul]

private lemma flux_test_density_pos {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {s : ℝ} (hs : 0 < s) (x : Vec d) :
    0 < anisotropicGaussian (homogenizedCoefficient Q) s x := by
  have hd := det_homogenizedCoefficient_pos Q
  unfold anisotropicGaussian
  exact mul_pos (div_pos (Real.rpow_pos_of_pos (by positivity) _)
    (Real.sqrt_pos.mpr hd)) (Real.exp_pos _)

/-- Division by the actual zero-force anisotropic kernel is everywhere defined. -/
lemma flux_test_kernel_ne_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) {s : ℝ} (hs : 0 < s) (x : Vec d) :
    homogenizedGaussianKernel Q i s hs 0 x ≠ 0 := by
  rw [homogenizedGaussianKernel_zero_eq_ofReal]
  exact Complex.ofReal_ne_zero.mpr (flux_test_density_pos Q hs x).ne'

/-- The test-to-kernel ratio is smooth in the original real coordinate carrier. -/
lemma flux_test_ratio_contDiff {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) {s : ℝ} (hs : 0 < s)
    (ψ : SchwartzMap (Vec d) ℂ) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x => ψ x / homogenizedGaussianKernel Q i s hs 0 x) := by
  simpa only [div_eq_mul_inv] using! (ψ.smooth ⊤).mul
    ((contDiff_homogenizedGaussianKernel_complexForce Q i s hs 0).inv
      (flux_test_kernel_ne_zero Q i hs))

/-- The quotient rule retains the literal inverse covariance in each coordinate. -/
lemma flux_test_ratio_fderiv_coordinate {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i j : Fin d) {s : ℝ} (hs : 0 < s)
    (ψ : SchwartzMap (Vec d) ℂ) (x : Vec d) :
    fderiv ℝ (fun y => ψ y / homogenizedGaussianKernel Q i s hs 0 y) x
        (unitVector j) =
      fderiv ℝ (fun y => ψ y) x (unitVector j) /
          homogenizedGaussianKernel Q i s hs 0 x +
        ((((homogenizedCoefficient Q)⁻¹).mulVec x j / s : ℝ) : ℂ) *
          (ψ x / homogenizedGaussianKernel Q i s hs 0 x) := by
  have hK := ((contDiff_homogenizedGaussianKernel_complexForce Q i s hs 0).differentiable
    (by simp)).differentiableAt (x := x)
  have hψ := ((ψ.smooth ⊤).differentiable (by simp)).differentiableAt (x := x)
  have hn := flux_test_kernel_ne_zero Q i hs x
  have hi := (differentiableAt_inv (𝕜 := ℝ) hn).comp x hK
  simp only [div_eq_mul_inv]
  erw [fderiv_fun_mul hψ hi, fderiv_comp x (differentiableAt_inv hn) hK,
    fderiv_inv' hn]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.neg_apply,
    ContinuousLinearMap.mulLeftRight_apply, smul_eq_mul, Function.comp_apply]
  rw [fderiv_homogenizedGaussianKernel_zero_coordinate]
  push_cast
  field_simp [hn]
  <;> ring

private lemma flux_test_kernel_inv_norm {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) {s : ℝ} (hs : 0 < s) (x : Vec d) :
    ‖homogenizedGaussianKernel Q i s hs 0 x‖⁻¹ =
      (2 * Real.pi * s) ^ ((d : ℝ) / 2) *
        Real.sqrt (homogenizedCoefficient Q).det *
          Real.exp (dot x ((homogenizedCoefficient Q)⁻¹.mulVec x) / (2 * s)) := by
  rw [homogenizedGaussianKernel_zero_eq_ofReal, Complex.norm_real,
    Real.norm_eq_abs, abs_of_pos (flux_test_density_pos Q hs x)]
  have hp : (2 * Real.pi * s) ^ (-(d : ℝ) / 2) =
      ((2 * Real.pi * s) ^ ((d : ℝ) / 2))⁻¹ := by
    rw [← Real.rpow_neg (by positivity : 0 ≤ 2 * Real.pi * s)]
    congr 1
    ring
  have he : -(∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k) /
      (2 * s) = -(dot x ((homogenizedCoefficient Q)⁻¹.mulVec x) / (2 * s)) := by
    simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
    ring
  unfold anisotropicGaussian
  rw [hp, he, Real.exp_neg]
  simp only [div_eq_mul_inv, mul_inv_rev, inv_inv]
  ring

private lemma flux_test_coord_abs_le {d : ℕ} (x : Vec d) (j : Fin d) :
    |x j| ≤ euclideanNorm x := by
  apply Real.abs_le_sqrt
  rw [sq]
  unfold euclideanSq dot
  exact Finset.single_le_sum (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ j)

private lemma flux_test_sqrt_det_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    Real.sqrt (homogenizedCoefficient Q).det ≤
      Real.sqrt ((d.factorial : ℝ) * (sourceReducedBound Λ₀) ^ d) := by
  apply Real.sqrt_le_sqrt
  have hentry (i j : Fin d) : |homogenizedCoefficient Q i j| ≤
      sourceReducedBound Λ₀ := by
    have h := (flux_test_coord_abs_le ((homogenizedCoefficient Q).mulVec
      (unitVector j)) i).trans (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q j)
    simpa [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using h
  have h := Matrix.det_le (abv := AbsoluteValue.abs)
    hentry
  exact (le_abs_self _).trans (by
    simpa only [AbsoluteValue.abs_apply, Fintype.card_fin, nsmul_eq_mul] using! h)

private lemma flux_test_linear_gaussian_absorption (u c : ℝ)
    (hc : 0 < c) : u * Real.exp (-c * u ^ 2) ≤ 1 + c⁻¹ := by
  have he : Real.exp (-c * u ^ 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr
      (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) (sq_nonneg _))
  have hlin : u ≤ 1 + u ^ 2 := by nlinarith [sq_nonneg (u - 1 / 2)]
  have hv : (c * u ^ 2) * Real.exp (-(c * u ^ 2)) ≤ 1 := by
    calc
      _ ≤ Real.exp (c * u ^ 2) * Real.exp (-(c * u ^ 2)) :=
        mul_le_mul_of_nonneg_right
          ((le_add_of_nonneg_right zero_le_one).trans (Real.add_one_le_exp _))
          (Real.exp_pos _).le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hv' : u ^ 2 * Real.exp (-c * u ^ 2) ≤ c⁻¹ := by
    apply (mul_le_mul_iff_of_pos_left hc).mp
    simpa only [mul_inv_cancel₀ hc.ne', ← mul_assoc, neg_mul] using hv
  nlinarith [mul_le_mul_of_nonneg_right hlin (Real.exp_pos (-c * u ^ 2)).le]

private lemma flux_test_scaled_linear_absorption (s c : ℝ) (hs : 0 < s)
    (hc : 0 < c) (n : ℝ) :
    (n / s) * Real.exp (-c * n ^ 2 / s) ≤
      (1 + c⁻¹) * s ^ (-(1 : ℝ) / 2) := by
  have hroot : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hp : s ^ (-(1 : ℝ) / 2) = (Real.sqrt s)⁻¹ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_neg hs.le]
    congr 1
    ring
  have he : -c * (n / Real.sqrt s) ^ 2 = -c * n ^ 2 / s := by
    rw [div_pow, Real.sq_sqrt hs.le]
    ring
  have hnscale : n / s = (n / Real.sqrt s) * (Real.sqrt s)⁻¹ := by
    calc
      n / s = n / (Real.sqrt s) ^ 2 := by rw [Real.sq_sqrt hs.le]
      _ = _ := by rw [pow_two, div_eq_mul_inv, mul_inv]; ring
  have h := mul_le_mul_of_nonneg_right
    (flux_test_linear_gaussian_absorption (n / Real.sqrt s) c hc)
    (inv_pos.mpr hroot).le
  rw [he] at h
  rw [hp, hnscale]
  simpa only [mul_assoc, mul_left_comm, mul_comm] using h

/-- A scalar Gaussian envelope can be divided by the actual broader kernel.
The covariance normalization is bounded before the scalar and the point. -/
private lemma flux_test_envelope_div_kernel {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (b s c α B : ℝ)
    (hb : 0 < b) (hs : 0 < s) (hB : 0 ≤ B)
    (hbc : sourceReducedBound Λ₀ ≤ b * c) (x : Vec d) (v : ℂ)
    (hv : ‖v‖ ≤ B * s ^ (-(d : ℝ) / 2 - α) *
      Real.exp (-c * euclideanNorm x ^ 2 / s)) :
    ‖v / homogenizedGaussianKernel Q i (b * s) (mul_pos hb hs) 0 x‖ ≤
      ((2 * Real.pi * b) ^ ((d : ℝ) / 2) *
        Real.sqrt ((d.factorial : ℝ) * (sourceReducedBound Λ₀) ^ d)) *
        B * s ^ (-α) * Real.exp (-(c / 2) * euclideanNorm x ^ 2 / s) := by
  let q := dot x ((homogenizedCoefficient Q)⁻¹.mulVec x)
  have hsq : euclideanNorm x ^ 2 = euclideanSq x := by
    apply Real.sq_sqrt
    unfold euclideanSq dot
    exact Finset.sum_nonneg (fun j _ => mul_self_nonneg (x j))
  have hq : q ≤ b * c * euclideanNorm x ^ 2 := by
    apply (homogenizedCoefficient_inv_quadratic_bounds Q x).2.trans
    rw [hsq]
    exact mul_le_mul_of_nonneg_right hbc (by rw [← hsq]; positivity)
  have hqdiv : q / (2 * (b * s)) ≤ c * euclideanNorm x ^ 2 / (2 * s) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * (b * s))
      (by positivity : 0 < 2 * s)).mpr
    nlinarith [mul_le_mul_of_nonneg_right hq (show 0 ≤ 2 * s by positivity)]
  have he : Real.exp (-c * euclideanNorm x ^ 2 / s + q / (2 * (b * s))) ≤
      Real.exp (-(c / 2) * euclideanNorm x ^ 2 / s) := by
    apply Real.exp_le_exp.mpr
    calc
      _ ≤ -c * euclideanNorm x ^ 2 / s + c * euclideanNorm x ^ 2 / (2 * s) :=
        add_le_add le_rfl hqdiv
      _ = _ := by simp only [div_eq_mul_inv, mul_inv_rev]; ring
  have hscale : s ^ (-(d : ℝ) / 2 - α) *
      (2 * Real.pi * (b * s)) ^ ((d : ℝ) / 2) =
        (2 * Real.pi * b) ^ ((d : ℝ) / 2) * s ^ (-α) := by
    rw [show 2 * Real.pi * (b * s) = (2 * Real.pi * b) * s by ring,
      Real.mul_rpow (by positivity) hs.le]
    rw [show s ^ (-(d : ℝ) / 2 - α) *
      ((2 * Real.pi * b) ^ ((d : ℝ) / 2) * s ^ ((d : ℝ) / 2)) =
      (2 * Real.pi * b) ^ ((d : ℝ) / 2) *
        (s ^ (-(d : ℝ) / 2 - α) * s ^ ((d : ℝ) / 2)) by ring,
      ← Real.rpow_add hs]
    congr 2
    ring
  rw [norm_div, div_eq_mul_inv, flux_test_kernel_inv_norm]
  change ‖v‖ * ((2 * Real.pi * (b * s)) ^ ((d : ℝ) / 2) *
    Real.sqrt (homogenizedCoefficient Q).det * Real.exp (q / (2 * (b * s)))) ≤ _
  calc
    _ ≤ (B * s ^ (-(d : ℝ) / 2 - α) * Real.exp (-c * euclideanNorm x ^ 2 / s)) *
        ((2 * Real.pi * (b * s)) ^ ((d : ℝ) / 2) *
          Real.sqrt (homogenizedCoefficient Q).det * Real.exp (q / (2 * (b * s)))) :=
      mul_le_mul_of_nonneg_right hv (by positivity)
    _ = (B * (s ^ (-(d : ℝ) / 2 - α) *
          (2 * Real.pi * (b * s)) ^ ((d : ℝ) / 2))) *
        (Real.sqrt (homogenizedCoefficient Q).det *
          Real.exp (-c * euclideanNorm x ^ 2 / s + q / (2 * (b * s)))) := by
      rw [Real.exp_add]
      ring
    _ ≤ (B * (s ^ (-(d : ℝ) / 2 - α) *
          (2 * Real.pi * (b * s)) ^ ((d : ℝ) / 2))) *
        (Real.sqrt ((d.factorial : ℝ) * (sourceReducedBound Λ₀) ^ d) *
          Real.exp (-(c / 2) * euclideanNorm x ^ 2 / s)) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul (flux_test_sqrt_det_le Q) he (Real.exp_pos _).le
          (Real.sqrt_nonneg _)) (by positivity)
    _ = _ := by rw [hscale]; ring

private lemma flux_test_inverse_coordinate_bound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (b s : ℝ) (hb : 1 ≤ b) (hs : 0 < s)
    (x : Vec d) (j : Fin d) :
    |((homogenizedCoefficient Q)⁻¹).mulVec x j / (b * s)| ≤
      sourceReducedBound Λ₀ * (euclideanNorm x / s) := by
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hn : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _
  have hK : 0 < sourceReducedBound Λ₀ := by
    have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
    unfold sourceReducedBound
    positivity
  rw [abs_div, abs_of_pos (mul_pos hb0 hs), ← mul_div_assoc]
  calc
    _ ≤ (sourceReducedBound Λ₀ * euclideanNorm x) / (b * s) :=
      div_le_div_of_nonneg_right
        ((flux_test_coord_abs_le _ j).trans
          (homogenizedCoefficient_inv_mulVec_bound Q x)) (by positivity)
    _ ≤ (sourceReducedBound Λ₀ * euclideanNorm x) / s :=
      div_le_div_of_nonneg_left (mul_nonneg hK.le hn) hs
        (by nlinarith)

private lemma flux_test_coordinate_square_sum (d : ℕ) (v : Fin d → ℂ)
    (M : ℝ) (hM : 0 ≤ M) (hv : ∀ j, ‖v j‖ ≤ M) :
    Real.sqrt (∑ j, ‖v j‖ ^ 2) ≤ Real.sqrt (d : ℝ) * M := by
  calc
    _ ≤ Real.sqrt (∑ _j : Fin d, M ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum (fun j _ => pow_le_pow_left₀ (norm_nonneg _) (hv j) 2)
    _ = Real.sqrt (d : ℝ) * M := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hM]

/-- A controlled Schwartz test divided by a uniformly broader actual Gaussian
has uniform value and Euclidean coordinate-gradient bounds. -/
theorem carverS_gaussian_test_ratio_bounds (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (ctest : ℝ) (hctest : 0 < ctest)
    (Btest : ℕ → ℝ) (hBtest : ∀ q, 0 < Btest q) :
    ∃ b C : ℝ, 1 ≤ b ∧ 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (s : ℝ), 1 ≤ s →
      ∀ (hbs : 0 < b * s) (k : ℕ) (ψ : SchwartzMap (Vec d) ℂ),
      HasGaussianTestControl s k ctest Btest ψ →
      let g : Vec d → ℂ := fun x =>
        ψ x / homogenizedGaussianKernel Q ⟨0, by omega⟩ (b * s) hbs 0 x
      ContDiff ℝ (⊤ : ℕ∞) g ∧ ∀ x : Vec d,
        ‖g x‖ ≤ C * Btest 0 * s ^ (-(k : ℝ) / 2) ∧
        Real.sqrt (∑ j : Fin d, ‖fderiv ℝ g x (unitVector j)‖ ^ 2) ≤
          C * (Btest 0 + Btest 1) * s ^ (-((k : ℝ) + 1) / 2) := by
  let K := sourceReducedBound D.ellipticity
  have hK : 0 < K := by
    have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one D.one_le_ellipticity
    dsimp [K]
    unfold sourceReducedBound
    positivity
  let b := 1 + K / ctest
  have hb : 1 ≤ b := by dsimp [b]; linarith [div_pos hK hctest]
  have hb0 : 0 < b := lt_of_lt_of_le zero_lt_one hb
  have hbc : K ≤ b * ctest := by
    dsimp [b]
    calc
      K = (K / ctest) * ctest := (div_mul_cancel₀ K hctest.ne').symm
      _ ≤ (1 + K / ctest) * ctest :=
        mul_le_mul_of_nonneg_right (by linarith) hctest.le
  let A := (2 * Real.pi * b) ^ ((d : ℝ) / 2) *
    Real.sqrt ((d.factorial : ℝ) * K ^ d)
  have hfac : 0 < (d.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos d
  have hA : 0 < A := by dsimp [A]; positivity
  let H := 1 + (ctest / 2)⁻¹
  have hH : 0 < H := by dsimp [H]; positivity
  have hB0 := hBtest 0
  have hB1 := hBtest 1
  let C₁ := A * (1 + K * H)
  have hC₁ : 0 < C₁ := by dsimp [C₁]; positivity
  let C := A + Real.sqrt (d : ℝ) * C₁ + 1
  have hC : 0 < C := by dsimp [C]; positivity
  have hAC : A ≤ C := by
    dsimp [C]
    nlinarith [mul_nonneg (Real.sqrt_nonneg (d : ℝ)) hC₁.le]
  have hCC : Real.sqrt (d : ℝ) * C₁ ≤ C := by dsimp [C]; linarith
  refine ⟨b, C, hb, hC, ?_⟩
  intro Q s hs hbs k ψ hψ
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  let i : Fin d := ⟨0, by omega⟩
  refine ⟨flux_test_ratio_contDiff Q i hbs ψ, ?_⟩
  intro x
  let E := Real.exp (-(ctest / 2) * euclideanNorm x ^ 2 / s)
  have hE : 0 ≤ E := (Real.exp_pos _).le
  have hE1 : E ≤ 1 := Real.exp_le_one_iff.mpr (by
    apply div_nonpos_of_nonpos_of_nonneg _ hs0.le
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (by positivity))
      (sq_nonneg _))
  have h0 : ‖ψ x / homogenizedGaussianKernel Q i (b * s) hbs 0 x‖ ≤
      A * Btest 0 * s ^ (-(k : ℝ) / 2) * E := by
    have hv := hψ 0 (fun j => Fin.elim0 j) x
    have h := flux_test_envelope_div_kernel Q i b s ctest ((k : ℝ) / 2)
      (Btest 0) hb0 hs0 (hBtest 0).le hbc x (ψ x)
      (by simpa only [iteratedFDeriv_zero_apply, Nat.zero_add] using hv)
    simpa only [A, K, E, neg_div] using h
  have h0' : ‖ψ x / homogenizedGaussianKernel Q i (b * s) hbs 0 x‖ ≤
      A * Btest 0 * s ^ (-(k : ℝ) / 2) :=
    h0.trans (mul_le_of_le_one_right (by positivity) hE1)
  have h1 (j : Fin d) :
      ‖fderiv ℝ (fun y => ψ y) x (unitVector j) /
        homogenizedGaussianKernel Q i (b * s) hbs 0 x‖ ≤
      A * Btest 1 * s ^ (-((k : ℝ) + 1) / 2) := by
    have hv := hψ 1 (fun _ => j) x
    have h := flux_test_envelope_div_kernel Q i b s ctest (((k : ℝ) + 1) / 2)
      (Btest 1) hb0 hs0 (hBtest 1).le hbc x
      (fderiv ℝ (fun y => ψ y) x (unitVector j))
      (by simpa only [iteratedFDeriv_one_apply, Nat.cast_add, Nat.cast_one, add_comm]
          using hv)
    have hh : ‖fderiv ℝ (fun y => ψ y) x (unitVector j) /
        homogenizedGaussianKernel Q i (b * s) hbs 0 x‖ ≤
        A * Btest 1 * s ^ (-((k : ℝ) + 1) / 2) * E := by
      simpa only [A, K, E, neg_div] using h
    exact hh.trans (mul_le_of_le_one_right (by positivity) hE1)
  have hpow : s ^ (-(k : ℝ) / 2) * s ^ (-(1 : ℝ) / 2) =
      s ^ (-((k : ℝ) + 1) / 2) := by
    rw [← Real.rpow_add hs0]
    congr 1
    ring
  have hw : (K * (euclideanNorm x / s)) *
      (A * Btest 0 * s ^ (-(k : ℝ) / 2) * E) ≤
        A * K * H * Btest 0 * s ^ (-((k : ℝ) + 1) / 2) := by
    calc
      _ = (A * K * Btest 0 * s ^ (-(k : ℝ) / 2)) *
          ((euclideanNorm x / s) * E) := by ring
      _ ≤ (A * K * Btest 0 * s ^ (-(k : ℝ) / 2)) *
          (H * s ^ (-(1 : ℝ) / 2)) :=
        mul_le_mul_of_nonneg_left
          (flux_test_scaled_linear_absorption s (ctest / 2) hs0 (by positivity)
            (euclideanNorm x)) (by positivity)
      _ = (A * K * H * Btest 0) *
          (s ^ (-(k : ℝ) / 2) * s ^ (-(1 : ℝ) / 2)) := by ring
      _ = _ := by rw [hpow]
  have hj (j : Fin d) :
      ‖fderiv ℝ (fun y => ψ y / homogenizedGaussianKernel Q i (b * s) hbs 0 y)
        x (unitVector j)‖ ≤
      C₁ * (Btest 0 + Btest 1) * s ^ (-((k : ℝ) + 1) / 2) := by
    rw [flux_test_ratio_fderiv_coordinate Q i j hbs ψ x]
    calc
      _ ≤ ‖fderiv ℝ (fun y => ψ y) x (unitVector j) /
          homogenizedGaussianKernel Q i (b * s) hbs 0 x‖ +
          |((homogenizedCoefficient Q)⁻¹).mulVec x j / (b * s)| *
            ‖ψ x / homogenizedGaussianKernel Q i (b * s) hbs 0 x‖ := by
        simpa only [norm_mul, Complex.norm_real, Real.norm_eq_abs] using norm_add_le
          (fderiv ℝ (fun y => ψ y) x (unitVector j) /
            homogenizedGaussianKernel Q i (b * s) hbs 0 x)
          (((((homogenizedCoefficient Q)⁻¹).mulVec x j / (b * s) : ℝ) : ℂ) *
            (ψ x / homogenizedGaussianKernel Q i (b * s) hbs 0 x))
      _ ≤ A * Btest 1 * s ^ (-((k : ℝ) + 1) / 2) +
          A * K * H * Btest 0 * s ^ (-((k : ℝ) + 1) / 2) :=
        add_le_add (h1 j) ((mul_le_mul
          (flux_test_inverse_coordinate_bound Q b s hb hs0 x j) h0
          (norm_nonneg _) (mul_nonneg hK.le
            (div_nonneg (Real.sqrt_nonneg _) hs0.le))).trans hw)
      _ ≤ _ := by
        dsimp [C₁]
        have hn : 0 ≤ A * Btest 0 * s ^ (-((k : ℝ) + 1) / 2) +
            A * K * H * Btest 1 * s ^ (-((k : ℝ) + 1) / 2) := by positivity
        nlinarith only [hn]
  refine ⟨h0'.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hAC (hBtest 0).le) (by positivity)), ?_⟩
  exact (flux_test_coordinate_square_sum d _ _ (by positivity) hj).trans (by
    have h := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hCC (show 0 ≤ Btest 0 + Btest 1 by positivity))
      (show 0 ≤ s ^ (-((k : ℝ) + 1) / 2) by positivity)
    simpa only [mul_assoc] using h)

/-- Uniform bounds for the actual finite centered Schwartz blocks pass to the
stationary average with the same fields and physical partition. The block
transfer must supply the finite bounds used by this assembly lemma. -/
lemma flux_schwartz_gain_of_finite_blocks {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {r : ℝ} (hr : 0 < r)
    (ψ : SchwartzMap (Vec d) ℂ) (J : Fin d → Lp ℂ 2 (reducedLaw Q))
    (p C : ℝ) (hC : 0 ≤ C)
    (hfinite : ∀ (j : Fin d) (Λ : Finset (Fin d → ℤ)),
      let b := fun z : Fin d → ℤ => centeredComplexLp Q (∫ y : Vec d,
        ((fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) : ℂ) * ψ (-y)) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J j));
      MemLp (∑ z ∈ Λ, (b z : FieldPair d → ℂ)) (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (∑ z ∈ Λ, (b z : FieldPair d → ℂ))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C) :
    (∀ j : Fin d, MemLp
      (stationarySchwartzAverage Q ψ (centeredComplexLp Q (J j)) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)) ∧
    Real.sqrt (∑ j : Fin d, ((eLpNorm
      (stationarySchwartzAverage Q ψ (centeredComplexLp Q (J j)) : FieldPair d → ℂ)
      (ENNReal.ofReal p) (reducedLaw Q)).toReal) ^ 2) ≤ Real.sqrt (d : ℝ) * C := by
  let b := fun (j : Fin d) (z : Fin d → ℤ) => centeredComplexLp Q (∫ y : Vec d,
    ((fluxPartitionCutoff r (y - fun i => r * (z i : ℝ)) : ℂ) * ψ (-y)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y (J j))
  have hscalar (j : Fin d) :
      MemLp (stationarySchwartzAverage Q ψ (centeredComplexLp Q (J j)) :
        FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) ∧
      (eLpNorm (stationarySchwartzAverage Q ψ (centeredComplexLp Q (J j)) :
        FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C := by
    apply flux_memLp_bound_of_tendsto (reducedLaw Q) p C hC
      (fun Λ => ∑ z ∈ Λ, b j z) _ _
      (flux_schwartz_centered_partition_hasSum Q hr ψ (J j))
    intro Λ
    have hh : MemLp (∑ z ∈ Λ, (b j z : FieldPair d → ℂ))
        (ENNReal.ofReal p) (reducedLaw Q) ∧
        (eLpNorm (∑ z ∈ Λ, (b j z : FieldPair d → ℂ))
          (ENNReal.ofReal p) (reducedLaw Q)).toReal ≤ C := by
      simpa only [b] using hfinite j Λ
    have he := Lp.coeFn_finsetSum Λ (b j)
    refine ⟨(memLp_congr_ae he).mpr hh.1, ?_⟩
    rw [eLpNorm_congr_ae he]
    exact hh.2
  refine ⟨fun j => (hscalar j).1, ?_⟩
  calc
    _ ≤ Real.sqrt (∑ _j : Fin d, C ^ 2) := by
      apply Real.sqrt_le_sqrt
      exact Finset.sum_le_sum fun j _ =>
        pow_le_pow_left₀ ENNReal.toReal_nonneg (hscalar j).2 2
    _ = Real.sqrt (d : ℝ) * C := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hC]

private lemma flux_test_euclidean_gradient (d : ℕ) (v : Fin d → ℝ) :
    euclideanNorm v = Real.sqrt (∑ j, (v j) ^ 2) := by
  simp only [euclideanNorm, euclideanSq, dot, pow_two]

private lemma flux_test_cutoff_gradient {d : ℕ} (χ f : Vec d → ℝ)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (U V H : ℝ) (hU : 0 ≤ U)
    (hχval : ∀ y, |χ y| ≤ 1)
    (hfval : ∀ y, |f y| ≤ U)
    (hχgrad : ∀ y, Real.sqrt (∑ j : Fin d,
      (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ H)
    (hfgrad : ∀ y, Real.sqrt (∑ j : Fin d,
      (fderiv ℝ f y (unitVector j)) ^ 2) ≤ V) (y : Vec d) :
    Real.sqrt (∑ j : Fin d,
      (fderiv ℝ (fun w => χ w * f w) y (unitVector j)) ^ 2) ≤ V + U * H := by
  have he : (fun j => fderiv ℝ (fun w => χ w * f w) y (unitVector j)) =
      χ y • (fun j => fderiv ℝ f y (unitVector j)) +
      f y • (fun j => fderiv ℝ χ y (unitVector j)) := by
    ext j
    change fderiv ℝ (χ * f) y (unitVector j) = _
    rw [((hχ.differentiable (by simp)).differentiableAt.hasFDerivAt.mul
      (hf.differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv]
    rfl
  rw [← flux_test_euclidean_gradient, he]
  calc
    _ ≤ euclideanNorm (χ y • (fun j => fderiv ℝ f y (unitVector j))) +
        euclideanNorm (f y • (fun j => fderiv ℝ χ y (unitVector j))) :=
      TimeChange.euclideanNorm_add_le _ _
    _ = |χ y| * Real.sqrt (∑ j, (fderiv ℝ f y (unitVector j)) ^ 2) +
        |f y| * Real.sqrt (∑ j, (fderiv ℝ χ y (unitVector j)) ^ 2) := by
      rw [TimeChange.euclideanNorm_smul, TimeChange.euclideanNorm_smul,
        flux_test_euclidean_gradient, flux_test_euclidean_gradient]
    _ ≤ 1 * V + U * H := add_le_add
      (mul_le_mul (hχval y) (hfgrad y) (Real.sqrt_nonneg _) (by norm_num))
      (mul_le_mul (hfval y) (hχgrad y) (Real.sqrt_nonneg _) hU)
    _ = V + U * H := by ring

/-- The actual normalized real and imaginary ratio cutoffs satisfy the physical
cutoff conditions, with constants chosen before the law, scales and test. -/
theorem carverS_gaussian_test_cutoff_admissible (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) (ctest : ℝ) (hctest : 0 < ctest)
    (Btest : ℕ → ℝ) (hBtest : ∀ q, 0 < Btest q) :
    ∃ b A : ℝ, 1 ≤ b ∧ 0 < A ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (s : ℝ), 1 ≤ s →
      ∀ (hbs : 0 < b * s) (k : ℕ) (ψ : SchwartzMap (Vec d) ℂ),
      HasGaussianTestControl s k ctest Btest ψ →
      ∀ (r : ℝ), 0 < r → ∀ (x z : Vec d) (χ : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) χ → HasCompactSupport χ →
      let R := 2 * Real.sqrt (d : ℝ) + 2;
      Function.support χ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} →
      (∀ y, |χ y| ≤ 1) →
      (∀ y, Real.sqrt (∑ j : Fin d, (fderiv ℝ χ y (unitVector j)) ^ 2) ≤ R / r) →
      let g : Vec d → ℂ := fun y =>
        ψ y / homogenizedGaussianKernel Q ⟨0, by omega⟩ (b * s) hbs 0 y;
      let M := A * (Btest 0 + Btest 1) * s ^ (-(k : ℝ) / 2) *
        (1 + r / Real.sqrt s);
      0 < M ∧ ∀ part : Bool,
        let θ : Vec d → ℝ := fun y => χ y *
          (if part then (g (x - (y + z))).re else (g (x - (y + z))).im) / M;
        ContDiff ℝ (⊤ : ℕ∞) θ ∧ HasCompactSupport θ ∧
        Function.support θ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} ∧
        (∀ y, |θ y| ≤ 1) ∧ ∀ y,
        Real.sqrt (∑ j : Fin d, (fderiv ℝ θ y (unitVector j)) ^ 2) ≤ R / r := by
  obtain ⟨b, C, hb, hC, hratio⟩ :=
    carverS_gaussian_test_ratio_bounds d hd D ctest hctest Btest hBtest
  refine ⟨b, 2 * C, hb, by positivity, ?_⟩
  intro Q s hs hbs k ψ hψ r hr x z χ hχ hcχ
  dsimp only
  intro hsupp hχval hχgrad
  let g : Vec d → ℂ := fun y =>
    ψ y / homogenizedGaussianKernel Q ⟨0, by omega⟩ (b * s) hbs 0 y
  let R := 2 * Real.sqrt (d : ℝ) + 2
  let S := s ^ (-(k : ℝ) / 2)
  let U := C * (Btest 0 + Btest 1) * S
  let M := 2 * C * (Btest 0 + Btest 1) * S * (1 + r / Real.sqrt s)
  have hs0 : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hsqrt : 0 < Real.sqrt s := Real.sqrt_pos.2 hs0
  have hB0 := hBtest 0
  have hB1 := hBtest 1
  have hS : 0 < S := Real.rpow_pos_of_pos hs0 _
  have hU : 0 < U := by dsimp [U]; positivity
  have hR : 1 ≤ R := by dsimp [R]; nlinarith [Real.sqrt_nonneg (d : ℝ)]
  have hM : 0 < M := by dsimp [M]; positivity
  have heM : M = 2 * U * (1 + r / Real.sqrt s) := by dsimp [M, U]; ring
  have hUM : U ≤ M := by
    rw [heM]
    nlinarith [div_pos hr hsqrt]
  have hnorm : U / Real.sqrt s + U * (R / r) ≤ M * (R / r) := by
    have hR0 : 0 ≤ R := le_trans zero_le_one hR
    have he : M * (R / r) = 2 * U * (R / r) + 2 * U * R / Real.sqrt s := by
      dsimp [M, U]
      field_simp
    rw [he]
    have h1 : 0 ≤ U * (R / r) := by positivity
    have h2 : U / Real.sqrt s ≤ 2 * U * R / Real.sqrt s := by
      apply div_le_div_of_nonneg_right _ hsqrt.le
      nlinarith
    linarith
  obtain ⟨hg, hgbound⟩ := hratio Q s hs hbs k ψ hψ
  change ContDiff ℝ (⊤ : ℕ∞) g at hg
  have hpow : s ^ (-((k : ℝ) + 1) / 2) = S / Real.sqrt s := by
    dsimp only [S]
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hs0]
    congr 1
    ring
  refine ⟨hM, ?_⟩
  intro part
  let π : ℂ →L[ℝ] ℝ := if part then Complex.reCLM else Complex.imCLM
  have hπ (w : ℂ) : |π w| ≤ ‖w‖ := by
    cases part <;> simp only [π, Bool.false_eq_true, ↓reduceIte,
      Complex.reCLM_apply, Complex.imCLM_apply]
    · exact Complex.abs_im_le_norm w
    · exact Complex.abs_re_le_norm w
  let f : Vec d → ℝ := fun y => π (g (x - (y + z)))
  have htrans : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => x - (y + z)) :=
    contDiff_const.sub (contDiff_id.add contDiff_const)
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := π.contDiff.comp (hg.comp htrans)
  have hfval (y : Vec d) : |f y| ≤ U := by
    apply (hπ _).trans
    exact (hgbound _).1.trans (by
      dsimp [U, S]
      gcongr
      exact le_add_of_nonneg_right (hBtest 1).le)
  have hfderiv (y : Vec d) (j : Fin d) :
      fderiv ℝ f y (unitVector j) = -π (fderiv ℝ g (x - (y + z)) (unitVector j)) := by
    have ht := (hasFDerivAt_const (𝕜 := ℝ) x y).sub
      ((hasFDerivAt_id (𝕜 := ℝ) y).add_const z)
    have hh := π.hasFDerivAt.comp y
      (((hg.differentiable (by simp)).differentiableAt.hasFDerivAt).comp y ht)
    simpa only [f, Function.comp_def, Pi.sub_apply, id_eq,
      ContinuousLinearMap.comp_apply, sub_apply,
      neg_apply, zero_apply,
      ContinuousLinearMap.id_apply, sub_zero, zero_sub, map_neg] using!
      congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector j)) hh.fderiv
  have hfgrad (y : Vec d) : Real.sqrt (∑ j : Fin d,
      (fderiv ℝ f y (unitVector j)) ^ 2) ≤ U / Real.sqrt s := by
    calc
      _ ≤ Real.sqrt (∑ j : Fin d, ‖fderiv ℝ g (x - (y + z)) (unitVector j)‖ ^ 2) := by
        apply Real.sqrt_le_sqrt
        apply Finset.sum_le_sum
        intro j _
        rw [hfderiv, neg_sq, ← sq_abs]
        exact pow_le_pow_left₀ (abs_nonneg _) (hπ _) 2
      _ ≤ U / Real.sqrt s := by
        have hh := (hgbound (x - (y + z))).2
        rw [hpow] at hh
        simpa only [U, mul_div_assoc] using hh
  let θ : Vec d → ℝ := fun y => χ y * f y / M
  have hpart (y : Vec d) :
      (if part then (g (x - (y + z))).re else (g (x - (y + z))).im) = f y := by
    cases part <;> rfl
  let θ₀ : Vec d → ℝ := fun y => χ y *
    (if part then (g (x - (y + z))).re else (g (x - (y + z))).im) / M
  change ContDiff ℝ (⊤ : ℕ∞) θ₀ ∧ HasCompactSupport θ₀ ∧
    Function.support θ₀ ⊆ {y : Vec d | euclideanNorm y ≤ R * r} ∧
    (∀ y, |θ₀ y| ≤ 1) ∧ ∀ y,
      Real.sqrt (∑ j : Fin d, (fderiv ℝ θ₀ y (unitVector j)) ^ 2) ≤ R / r
  have heθ : θ₀ = θ := by
    funext y
    exact congrArg (fun a : ℝ => χ y * a / M) (hpart y)
  rw [heθ]
  have hθ : θ = fun y => M⁻¹ * (χ y * f y) := by
    funext y
    dsimp [θ]
    ring
  have hsub : Function.support θ ⊆ Function.support χ := by
    intro y hy
    by_contra hyχ
    have hz : χ y = 0 := by simpa only [Function.mem_support, not_not] using hyχ
    exact hy (by simp only [θ, hz, zero_mul, zero_div])
  refine ⟨by rw [hθ]; exact contDiff_const.mul (hχ.mul hf), ?_,
    hsub.trans hsupp, ?_, ?_⟩
  · exact hcχ.mono hsub
  · intro y
    dsimp [θ]
    rw [abs_div, abs_of_pos hM]
    apply (div_le_one hM).2
    rw [abs_mul]
    calc
      _ ≤ 1 * U := mul_le_mul (hχval y) (hfval y) (abs_nonneg _) zero_le_one
      _ ≤ M := by simpa only [one_mul] using hUM
  · intro y
    have hprod := flux_test_cutoff_gradient χ f hχ hf U (U / Real.sqrt s) (R / r)
      hU.le hχval hfval hχgrad hfgrad y
    have hderiv (j : Fin d) : fderiv ℝ θ y (unitVector j) =
        M⁻¹ * fderiv ℝ (fun w => χ w * f w) y (unitVector j) := by
      rw [hθ]
      change fderiv ℝ ((fun _ : Vec d => M⁻¹) * (fun w => χ w * f w)) y
        (unitVector j) = _
      rw [((hasFDerivAt_const (M⁻¹) y).mul
        ((hχ.mul hf).differentiable (by simp)).differentiableAt.hasFDerivAt).fderiv]
      simp
    calc
      _ = M⁻¹ * Real.sqrt (∑ j : Fin d,
          (fderiv ℝ (fun w => χ w * f w) y (unitVector j)) ^ 2) := by
        rw [← flux_test_euclidean_gradient]
        simp_rw [hderiv]
        change euclideanNorm (M⁻¹ • (fun j =>
          fderiv ℝ (fun w => χ w * f w) y (unitVector j))) = _
        rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.2 hM),
          flux_test_euclidean_gradient]
      _ ≤ M⁻¹ * (M * (R / r)) :=
        mul_le_mul_of_nonneg_left (hprod.trans hnorm) (inv_nonneg.2 hM.le)
      _ = R / r := by rw [← mul_assoc, inv_mul_cancel₀ hM.ne', one_mul]

/-- The average of adjacent lattice cutoffs is an actual smooth partition
with a pointwise margin of one half and the sharp Euclidean gradient bound. -/
theorem carverS_flux_lattice_partition_with_slack (d : ℕ) (hd : 2 ≤ d)
    (j : Fin d) (r : ℝ) (hr : 0 < r) :
    let v : Vec d := r • unitVector j
    let χ : Vec d → ℝ := fun y =>
      (fluxPartitionCutoff r y + fluxPartitionCutoff r (y - v)) / 2
    ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
    Function.support χ ⊆
      {y : Vec d | euclideanNorm y ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
    (∀ y, 0 ≤ χ y ∧ χ y ≤ 1 / 2) ∧
    (∀ y, Real.sqrt (∑ k : Fin d, (fderiv ℝ χ y (unitVector k)) ^ 2) ≤
      Real.sqrt (d : ℝ) / r) ∧
    ∀ y, HasSum (fun z : Fin d → ℤ => χ (y - fun k => r * (z k : ℝ))) 1 := by
  let v : Vec d := r • unitVector j
  let χ : Vec d → ℝ := fun y =>
    (fluxPartitionCutoff r y + fluxPartitionCutoff r (y - v)) / 2
  change ContDiff ℝ (⊤ : ℕ∞) χ ∧ HasCompactSupport χ ∧
    Function.support χ ⊆ {y | euclideanNorm y ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
    (∀ y, 0 ≤ χ y ∧ χ y ≤ 1 / 2) ∧
    (∀ y, Real.sqrt (∑ k : Fin d, (fderiv ℝ χ y (unitVector k)) ^ 2) ≤
      Real.sqrt (d : ℝ) / r) ∧
    ∀ y, HasSum (fun z : Fin d → ℤ => χ (y - fun k => r * (z k : ℝ))) 1
  have hd0 : 0 ≤ (d : ℝ) := by exact_mod_cast (Nat.zero_le 2).trans hd
  have hf := flux_partition_cutoff_contDiff (d := d) r
  have ht : ContDiff ℝ (⊤ : ℕ∞) (fun y : Vec d => fluxPartitionCutoff r (y - v)) :=
    hf.comp (contDiff_id.sub contDiff_const)
  have hc := flux_partition_cutoff_hasCompactSupport (d := d) hr
  have hct : HasCompactSupport (fun y : Vec d => fluxPartitionCutoff r (y - v)) := by
    exact hc.comp_homeomorph (Homeomorph.addRight (-v))
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := (hf.add ht).div_const 2
  refine ⟨hχ, ?_, ?_, ?_, ?_, ?_⟩
  · apply (hc.add hct).mono
    intro y hy hzero
    change fluxPartitionCutoff r y + fluxPartitionCutoff r (y - v) = 0 at hzero
    exact hy (by change (_ + _) / 2 = 0; rw [hzero]; norm_num)
  · intro y hy
    have hv : euclideanNorm v = r := by
      dsimp only [v]
      rw [TimeChange.euclideanNorm_smul, euclideanNorm_unitVector_eq_one,
        abs_of_pos hr, mul_one]
    have hcases : fluxPartitionCutoff r y ≠ 0 ∨
        fluxPartitionCutoff r (y - v) ≠ 0 := by
      by_contra h
      push Not at h
      exact hy (by simp only [χ, h.1, h.2, zero_add, zero_div])
    rcases hcases with h | h
    · have hb : euclideanNorm y ≤ 2 * Real.sqrt (d : ℝ) * r :=
        flux_partition_cutoff_support_sharp hr h
      change euclideanNorm y ≤ (2 * Real.sqrt (d : ℝ) + 2) * r
      nlinarith only [hb, hr]
    · have hb : euclideanNorm (y - v) ≤ 2 * Real.sqrt (d : ℝ) * r :=
        flux_partition_cutoff_support_sharp hr h
      have hn : euclideanNorm y ≤ euclideanNorm (y - v) + r := by
        simpa only [sub_add_cancel, hv] using TimeChange.euclideanNorm_add_le (y - v) v
      change euclideanNorm y ≤ (2 * Real.sqrt (d : ℝ) + 2) * r
      nlinarith only [hb, hn, hr]
  · intro y
    exact ⟨div_nonneg (add_nonneg (flux_partition_cutoff_nonneg r y)
      (flux_partition_cutoff_nonneg r (y - v))) (by norm_num),
      div_le_div_of_nonneg_right (c3_flux_partition_two_translate_le_one hr j y)
        (by norm_num)⟩
  · intro y
    have hder (k : Fin d) : fderiv ℝ χ y (unitVector k) =
        (fderiv ℝ (fluxPartitionCutoff r) y (unitVector k) +
          fderiv ℝ (fluxPartitionCutoff r) (y - v) (unitVector k)) / 2 := by
      have h0 := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt (x := y)
      have h1 := (hf.differentiable (by simp)).differentiableAt.hasFDerivAt (x := y - v)
      have ht1 : HasFDerivAt (fun w : Vec d => fluxPartitionCutoff r (w - v))
          (fderiv ℝ (fluxPartitionCutoff r) (y - v)) y := by
        simpa only [Function.comp_def, ContinuousLinearMap.comp_id] using!
          h1.comp y ((hasFDerivAt_id y).sub_const v)
      have hχd : HasFDerivAt χ ((2 : ℝ)⁻¹ •
          (fderiv ℝ (fluxPartitionCutoff r) y +
            fderiv ℝ (fluxPartitionCutoff r) (y - v))) y := by
        simpa only [χ, div_eq_mul_inv, Pi.add_apply] using!
          (h0.add ht1).mul_const (2 : ℝ)⁻¹
      rw [hχd.fderiv]
      simp only [smul_apply, add_apply,
        smul_eq_mul, div_eq_mul_inv, mul_comm]
    have hcoord (k : Fin d) : |fderiv ℝ χ y (unitVector k)| ≤ 1 / r := by
      rw [hder, abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
      have hsum := (abs_add_le
        (fderiv ℝ (fluxPartitionCutoff r) y (unitVector k))
        (fderiv ℝ (fluxPartitionCutoff r) (y - v) (unitVector k))).trans
          (add_le_add (flux_partition_cutoff_coord_deriv_le hr y k)
            (flux_partition_cutoff_coord_deriv_le hr (y - v) k))
      linarith only [hsum]
    have hs : ∑ k : Fin d, (fderiv ℝ χ y (unitVector k)) ^ 2 ≤
        (d : ℝ) * (1 / r) ^ 2 := by
      calc
        _ ≤ ∑ _k : Fin d, (1 / r) ^ 2 := by
          apply Finset.sum_le_sum
          intro k _
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) (hcoord k) 2
        _ = _ := by simp
    calc
      _ ≤ Real.sqrt ((d : ℝ) * (1 / r) ^ 2) := Real.sqrt_le_sqrt hs
      _ = Real.sqrt (d : ℝ) / r := by
        rw [Real.sqrt_mul hd0, Real.sqrt_sq (by positivity : 0 ≤ 1 / r)]
        ring
  · intro y
    have hsum := ((flux_partition_cutoff_partition hr y).add
      (flux_partition_cutoff_partition hr (y - v))).mul_right ((2 : ℝ)⁻¹)
    have harg (z : Fin d → ℤ) :
        (y - fun k => r * (z k : ℝ)) - v =
          (y - v) - fun k => r * (z k : ℝ) := by
      ext k
      simp only [Pi.sub_apply]
      ring
    convert hsum using 1
    · simp only [χ, div_eq_mul_inv, harg]
    · norm_num

/-- A compact zero-periodization perturbation preserves the actual partition
and its admissible physical-scale bounds under explicit amplitude margins. -/
theorem carverS_flux_partition_perturbation_admissible (d : ℕ) (hd : 2 ≤ d)
    (j : Fin d) (r : ℝ) (hr : 0 < r) (h : Vec d → ℝ)
    (hh : ContDiff ℝ (⊤ : ℕ∞) h) (hhc : HasCompactSupport h)
    (hsupp : Function.support h ⊆
      {y : Vec d | euclideanNorm y ≤ (2 * Real.sqrt (d : ℝ) + 2) * r})
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B) (hval : ∀ y, |h y| ≤ A)
    (hgrad : ∀ y, Real.sqrt (∑ k : Fin d, (fderiv ℝ h y (unitVector k)) ^ 2) ≤ B / r)
    (hzero : ∀ y, HasSum (fun z : Fin d → ℤ => h (y - fun k => r * (z k : ℝ))) 0)
    (c : ℝ) (hcA : |c| * A ≤ 1 / 2) (hcB : |c| * B ≤ Real.sqrt (d : ℝ) + 2) :
    let v : Vec d := r • unitVector j
    let θ : Vec d → ℝ := fun y =>
      (fluxPartitionCutoff r y + fluxPartitionCutoff r (y - v)) / 2 + c * h y
    ContDiff ℝ (⊤ : ℕ∞) θ ∧ HasCompactSupport θ ∧
    Function.support θ ⊆
      {y : Vec d | euclideanNorm y ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
    (∀ y, |θ y| ≤ 1) ∧
    (∀ y, Real.sqrt (∑ k : Fin d, (fderiv ℝ θ y (unitVector k)) ^ 2) ≤
      (2 * Real.sqrt (d : ℝ) + 2) / r) ∧
    ∀ y, HasSum (fun z : Fin d → ℤ => θ (y - fun k => r * (z k : ℝ))) 1 := by
  let v : Vec d := r • unitVector j
  let χ : Vec d → ℝ := fun y =>
    (fluxPartitionCutoff r y + fluxPartitionCutoff r (y - v)) / 2
  let θ : Vec d → ℝ := fun y => χ y + c * h y
  obtain ⟨hχ, hχc, hχs, hχv, hχg, hχp⟩ :=
    carverS_flux_lattice_partition_with_slack d hd j r hr
  change ContDiff ℝ (⊤ : ℕ∞) θ ∧ _
  have hch : ContDiff ℝ (⊤ : ℕ∞) (fun y => c * h y) := contDiff_const.mul hh
  have hcch : HasCompactSupport (fun y => c * h y) := hhc.mul_left
  refine ⟨hχ.add hch, hχc.add hcch, ?_, ?_, ?_, ?_⟩
  · intro y hy
    by_cases hχy : χ y = 0
    · apply hsupp
      intro hhy
      exact hy (by change χ y + c * h y = 0; rw [hχy, hhy]; ring)
    · exact hχs hχy
  · intro y
    have hχabs : |χ y| ≤ 1 / 2 := by
      rw [abs_of_nonneg (hχv y).1]
      exact (hχv y).2
    calc
      |θ y| ≤ |χ y| + |c * h y| := abs_add_le _ _
      _ = |χ y| + |c| * |h y| := by rw [abs_mul]
      _ ≤ 1 / 2 + |c| * A := add_le_add hχabs
        (by
          simpa only [mul_comm] using
            mul_le_mul (hval y) (le_refl |c|) (abs_nonneg c) hA)
      _ ≤ 1 := by linarith only [hcA]
  · intro y
    have he : (fun k => fderiv ℝ θ y (unitVector k)) =
        (fun k => fderiv ℝ χ y (unitVector k)) +
          c • (fun k => fderiv ℝ h y (unitVector k)) := by
      ext k
      have hθd : HasFDerivAt θ
          (fderiv ℝ χ y + c • fderiv ℝ h y) y := by
        simpa only [θ, Pi.add_apply] using!
          (((hχ.differentiable (by simp)).differentiableAt.hasFDerivAt).add
            (((hh.differentiable (by simp)).differentiableAt.hasFDerivAt).const_mul c))
      rw [hθd.fderiv]
      rfl
    rw [← flux_test_euclidean_gradient, he]
    calc
      _ ≤ euclideanNorm (fun k => fderiv ℝ χ y (unitVector k)) +
          euclideanNorm (c • (fun k => fderiv ℝ h y (unitVector k))) :=
        TimeChange.euclideanNorm_add_le _ _
      _ = Real.sqrt (∑ k : Fin d, (fderiv ℝ χ y (unitVector k)) ^ 2) +
          |c| * Real.sqrt (∑ k : Fin d, (fderiv ℝ h y (unitVector k)) ^ 2) := by
        rw [TimeChange.euclideanNorm_smul, flux_test_euclidean_gradient,
          flux_test_euclidean_gradient]
      _ ≤ Real.sqrt (d : ℝ) / r + |c| * (B / r) :=
        add_le_add (hχg y) (by
          simpa only [mul_comm] using
            mul_le_mul (hgrad y) (le_refl |c|) (abs_nonneg c) (div_nonneg hB hr.le))
      _ = (Real.sqrt (d : ℝ) + |c| * B) / r := by ring
      _ ≤ (2 * Real.sqrt (d : ℝ) + 2) / r :=
        div_le_div_of_nonneg_right (by
          linarith only [hcB]) hr.le
  · intro y
    simpa only [mul_zero, add_zero] using (hχp y).add ((hzero y).mul_left c)


/-- Both real components of a complex zero-periodization perturbation yield
admissible perturbations of the canonical lattice partition. -/
theorem carverS_flux_complex_partition_perturbations_admissible
    (d : ℕ) (hd : 2 ≤ d) (j : Fin d) (r : ℝ) (hr : 0 < r)
    (h : Vec d → ℂ) (hh : ContDiff ℝ (⊤ : ℕ∞) h)
    (hhc : HasCompactSupport h)
    (hsupp : Function.support h ⊆
      {y : Vec d | euclideanNorm y ≤ (2 * Real.sqrt (d : ℝ) + 2) * r})
    (A B : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hval : ∀ y, ‖h y‖ ≤ A)
    (hgrad : ∀ y, Real.sqrt (∑ k : Fin d,
      ‖fderiv ℝ h y (unitVector k)‖ ^ 2) ≤ B / r)
    (hzero : ∀ y, HasSum (fun z : Fin d → ℤ =>
      h (y - fun k => r * (z k : ℝ))) 0)
    (c : ℝ) (hcA : |c| * A ≤ 1 / 2)
    (hcB : |c| * B ≤ Real.sqrt (d : ℝ) + 2) :
    let v : Vec d := r • unitVector j
    let θ : Bool → Vec d → ℝ := fun b y =>
      (fluxPartitionCutoff r y + fluxPartitionCutoff r (y - v)) / 2 +
        c * (if b then (h y).im else (h y).re)
    ∀ b, ContDiff ℝ (⊤ : ℕ∞) (θ b) ∧ HasCompactSupport (θ b) ∧
      Function.support (θ b) ⊆
        {y : Vec d | euclideanNorm y ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
      (∀ y, |θ b y| ≤ 1) ∧
      (∀ y, Real.sqrt (∑ k : Fin d,
        (fderiv ℝ (θ b) y (unitVector k)) ^ 2) ≤
          (2 * Real.sqrt (d : ℝ) + 2) / r) ∧
      ∀ y, HasSum (fun z : Fin d → ℤ =>
        θ b (y - fun k => r * (z k : ℝ))) 1 := by
  dsimp only
  intro b
  let L : ℂ →L[ℝ] ℝ := if b then RCLike.imCLM else RCLike.reCLM
  have hL : ∀ z, |L z| ≤ ‖z‖ := by
    intro z
    cases b <;> simp only [L, Bool.false_eq_true, ↓reduceIte, RCLike.reCLM_apply,
      RCLike.imCLM_apply]
    · exact Complex.abs_re_le_norm z
    · exact Complex.abs_im_le_norm z
  obtain ⟨hp, hpc, hps, hpv, hpg⟩ :=
    c3_complex_cutoff_real_projection h L hL hh hhc _ A (B / r) hsupp hval hgrad
  have hpzero : ∀ y, HasSum (fun z : Fin d → ℤ =>
      L (h (y - fun k => r * (z k : ℝ)))) 0 := by
    intro y
    simpa using L.hasSum (hzero y)
  have hpg' : ∀ y, Real.sqrt (∑ k : Fin d,
      (fderiv ℝ (fun x => L (h x)) y (unitVector k)) ^ 2) ≤ B / r := by
    intro y
    simpa only [sq_abs] using hpg y
  have result := carverS_flux_partition_perturbation_admissible d hd j r hr
    (fun x => L (h x)) hp hpc hps A B hA hB hpv hpg' hpzero c hcA hcB
  cases b <;> simpa [L] using result


/-- Four normalized zero-periodic perturbations produce admissible partitions. -/
theorem carverS_flux_normalized_partition_family_admissible
    (d : ℕ) (hd : 2 ≤ d) (j : Fin d) (r : ℝ) (hr : 0 < r)
    (h : Bool → Bool → Vec d → ℝ)
    (hh : ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (h b q) ∧ HasCompactSupport (h b q) ∧
      Function.support (h b q) ⊆
        {w : Vec d | euclideanNorm w ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
      (∀ w, |h b q w| ≤ 1 / 2) ∧
      (∀ w, Real.sqrt (∑ k : Fin d, (fderiv ℝ (h b q) w (unitVector k)) ^ 2) ≤
        1 / (2 * r)) ∧
      ∀ y, HasSum (fun z : Fin d → ℤ => h b q (y - fun k => r * (z k : ℝ))) 0) :
    let v := r • unitVector j
    let θ : Bool → Bool → Vec d → ℝ := fun b q w =>
      (fluxPartitionCutoff r w + fluxPartitionCutoff r (w - v)) / 2 + h b q w
    ∀ b q, ContDiff ℝ (⊤ : ℕ∞) (θ b q) ∧ HasCompactSupport (θ b q) ∧
      Function.support (θ b q) ⊆
        {w : Vec d | euclideanNorm w ≤ (2 * Real.sqrt (d : ℝ) + 2) * r} ∧
      (∀ w, |θ b q w| ≤ 1) ∧
      (∀ w, Real.sqrt (∑ k : Fin d, (fderiv ℝ (θ b q) w (unitVector k)) ^ 2) ≤
        (2 * Real.sqrt (d : ℝ) + 2) / r) ∧
      ∀ y, HasSum (fun z : Fin d → ℤ => θ b q (y - fun k => r * (z k : ℝ))) 1 := by
  dsimp only
  intro b q
  obtain ⟨hreg, hcompact, hsupp, hval, hgrad, hzero⟩ := hh b q
  have hg : ∀ w, Real.sqrt (∑ k : Fin d,
      (fderiv ℝ (h b q) w (unitVector k)) ^ 2) ≤ (1 / 2 : ℝ) / r := by
    intro w
    convert hgrad w using 1 <;> ring
  have result := carverS_flux_partition_perturbation_admissible d hd j r hr
    (h b q) hreg hcompact hsupp (1 / 2) (1 / 2) (by norm_num) (by norm_num)
    hval hg hzero 1 (by norm_num) (by have := Real.sqrt_nonneg (d : ℝ); norm_num; linarith)
  simpa using result


end EinsteinFull.Blueprint
