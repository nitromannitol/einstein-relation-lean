import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedClockObservation
import EinsteinFull.Work.W4.HomogeneousGaussianTimeDerivativeBoundSupport
import EinsteinFull.Work.W4.HomogeneousGaussianTimeIntegralSupport
import EinsteinFull.Work.W7.ClockFiniteRangeSupport
import EinsteinFull.Work.W7.ClockCovarianceLimitProof
import EinsteinFull.Calculus.ComplexHorizontalIntegrationSupport
import EinsteinFull.Calculus.ComplexLpSupport

open EinsteinRelation MeasureTheory
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull.Blueprint

/-- Finite-range clock covariance gives spatial decay for the literal forced Gaussian derivative. -/
theorem clock_gaussian_time_derivative_decay
    : ∀ (d : ℕ) (D : StructuralData d), ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ (i : Fin d) (ζ : ℂ) (t : ℝ), 0 < t →
        ‖homogeneousGaussianEvolutionTimeDerivative Q i ζ (centeredComplexLp Q μ) t‖ ≤
          C * (t⁻¹ + ‖ζ‖ ^ 2) * Real.exp (C * ‖ζ‖ ^ 2 * t) * t ^ (-(d : ℝ) / 4) := by
  have hpair : ∀ {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
      (u : Lp ℂ 2 (reducedLaw Q)),
      ((u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        fun ω => (centeredClockField Q 0 ω : ℂ)) →
      ∀ (f : Vec d → ℂ), Continuous f → Integrable f →
      ∀ B : ℝ, (∀ x, ‖f x‖ ≤ B) →
      ‖complexClockSpatialPairing Q u f‖ ^ 2 ≤
        clockVarianceConstant d Λ r * B * (∫ x, ‖f x‖) := by
    intro d Λ r Q u hu f hfc hf B hB
    have hustar : star u = u := by
      apply Lp.ext
      filter_upwards [Lp.coeFn_star u, hu] with ω hs hω
      rw [hs]
      change star (u ω) = u ω
      rw [hω]
      simp
    let K : Lp ℂ 2 (reducedLaw Q) →L[ℝ] Lp ℂ 2 (reducedLaw Q) :=
      Complex.conjCLE.toContinuousLinearMap.compLpL 2 (reducedLaw Q)
    have hK (v : Lp ℂ 2 (reducedLaw Q)) : K v = star v := by
      apply Lp.ext
      filter_upwards [Complex.conjCLE.toContinuousLinearMap.coeFn_compLpL v,
        Lp.coeFn_star v] with ω h₁ h₂
      exact h₁.trans h₂.symm
    have hstar : star (complexClockSpatialPairing Q u f) =
        complexClockSpatialPairing Q u (fun x => star (f x)) := by
      rw [← hK]
      unfold complexClockSpatialPairing
      rw [← K.integral_comp_comm
        (integrable_kernel_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
          f hf hfc u)]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun x => by
        dsimp only
        rw [hK]
        have hsm (c : ℂ) (v : Lp ℂ 2 (reducedLaw Q)) :
            star (c • v) = star c • star v := by
          apply Lp.ext
          filter_upwards [Lp.coeFn_star (c • v), Lp.coeFn_smul c v,
            Lp.coeFn_smul (star c) (star v), Lp.coeFn_star v] with ω h₁ h₂ h₃ h₄
          change (star (c • v)) ω = star ((c • v) ω) at h₁
          change (star c • star v) ω = star c * (star v) ω at h₃
          change (star v) ω = star (v ω) at h₄
          change (c • v) ω = c * v ω at h₂
          rw [h₁, h₂, h₃, h₄, star_mul]
          ring
        rw [hsm, ← complexTranslation_star, hustar]
    have hcov := integral_complexClockSpatialPairing_mul_eq_convolution Q hu
      hfc.star hfc (Complex.conjCLE.toContinuousLinearMap.integrable_comp hf) hf
    have hnorm : ‖complexClockSpatialPairing Q u f‖ ^ 2 =
        ‖∫ ω, complexClockSpatialPairing Q u (fun x => star (f x)) ω *
          complexClockSpatialPairing Q u f ω ∂reducedLaw Q‖ := by
      rw [← hstar]
      have he : (∫ ω, (star (complexClockSpatialPairing Q u f)) ω *
          complexClockSpatialPairing Q u f ω ∂reducedLaw Q) =
          inner ℂ (complexClockSpatialPairing Q u f) (complexClockSpatialPairing Q u f) := by
        rw [L2.inner_def]
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_star (complexClockSpatialPairing Q u f)] with ω hω
        rw [hω]
        change star ((complexClockSpatialPairing Q u f) ω) * _ = _
        simp only [RCLike.inner_apply', starRingEnd_apply]
      simp only [he, inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal,
        abs_of_nonneg (norm_nonneg _)]
    rw [hnorm, hcov]
    calc
      _ ≤ ∫ z : Vec d, |clockCovarianceKernel Q z| * (B * ∫ x, ‖f x‖) := by
        apply norm_integral_le_of_norm_le
          ((integrable_clockCovarianceKernel Q).abs.mul_const _)
        exact Filter.Eventually.of_forall fun z => by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          rw [← integral_const_mul]
          apply norm_integral_le_of_norm_le (hf.norm.const_mul B)
          exact Filter.Eventually.of_forall fun x => by
            rw [norm_mul, norm_star, mul_comm B]
            exact mul_le_mul_of_nonneg_left (hB (x + z)) (norm_nonneg _)
      _ = (∫ z, |clockCovarianceKernel Q z|) * (B * ∫ x, ‖f x‖) :=
        integral_mul_const _ _
      _ ≤ clockVarianceConstant d Λ r * B * (∫ x, ‖f x‖) := by
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_right (integral_abs_clockCovarianceKernel_le Q)
          (mul_nonneg ((norm_nonneg (f 0)).trans (hB 0))
            (integral_nonneg fun _ => norm_nonneg _))
  have hgauss : ∀ {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
      (t : ℝ) (ht : 0 < t) (x : Vec d),
      0 ≤ anisotropicGaussian (homogenizedCoefficient Q) (4 * t) x ∧
      anisotropicGaussian (homogenizedCoefficient Q) (4 * t) x ≤
        ((8 * Real.pi) ^ (-(d : ℝ) / 2) *
          Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ ^ d)) *
          t ^ (-(d : ℝ) / 2) := by
    intro d Λ r Q t ht x
    have hq : 0 ≤ ∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k := by
      have h := (homogenizedCoefficient_inv_quadratic_bounds Q x).1
      have hx : 0 ≤ euclideanSq x := by
        unfold euclideanSq dot
        exact Finset.sum_nonneg fun j _ => mul_self_nonneg _
      have hK : 0 < sourceReducedBound Λ := by
        unfold sourceReducedBound
        exact mul_pos (Real.exp_pos _)
          (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ])
      have he : (∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k) =
          dot x ((homogenizedCoefficient Q)⁻¹.mulVec x) := by
        simp only [dot, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
      rw [he]
      exact (mul_nonneg (inv_nonneg.mpr hK.le) hx).trans h
    have hscale : (2 * Real.pi * (4 * t)) ^ (-(d : ℝ) / 2) =
        (8 * Real.pi) ^ (-(d : ℝ) / 2) * t ^ (-(d : ℝ) / 2) := by
      rw [show 2 * Real.pi * (4 * t) = (8 * Real.pi) * t by ring]
      exact Real.mul_rpow (by positivity) ht.le
    constructor
    · unfold anisotropicGaussian
      positivity
    · unfold anisotropicGaussian
      calc
        _ ≤ (2 * Real.pi * (4 * t)) ^ (-(d : ℝ) / 2) /
            Real.sqrt (homogenizedCoefficient Q).det := by
          apply mul_le_of_le_one_right (by positivity)
          exact Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hq)
            (by positivity))
        _ ≤ _ := by
          rw [div_eq_mul_inv, hscale, mul_right_comm _ (t ^ _)]
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (inv_sqrt_det_homogenizedCoefficient_le Q)
              (by positivity)) (by positivity)
  have hdom : ∀ {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
      (u : Lp ℂ 2 (reducedLaw Q)),
      ((u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        fun ω => (centeredClockField Q 0 ω : ℂ)) →
      ∀ (f : Vec d → ℂ), Continuous f → Integrable f →
      ∀ (w : Vec d → ℝ), Integrable w → (∫ x, w x) = 1 →
      ∀ (a b : ℝ), 0 ≤ a → 0 ≤ b →
      (∀ x, w x ≤ b) → (∀ x, ‖f x‖ ≤ a * w x) →
      ‖complexClockSpatialPairing Q u f‖ ≤
        a * Real.sqrt (clockVarianceConstant d Λ r * b) := by
    intro d Λ r Q u hu f hfc hf w hw hw1 a b ha hb hwb hfw
    have hV : 0 ≤ clockVarianceConstant d Λ r := by
      exact (integral_nonneg fun z => abs_nonneg (clockCovarianceKernel Q z)).trans
        (integral_abs_clockCovarianceKernel_le Q)
    have hfB (x : Vec d) : ‖f x‖ ≤ a * b :=
      (hfw x).trans (mul_le_mul_of_nonneg_left (hwb x) ha)
    have hI : (∫ x, ‖f x‖) ≤ a := by
      calc
        _ ≤ ∫ x, a * w x := integral_mono hf.norm (hw.const_mul a) hfw
        _ = a := by rw [integral_const_mul, hw1, mul_one]
    have hsq := (hpair Q u hu f hfc hf (a * b) hfB).trans
      (mul_le_mul_of_nonneg_left hI (mul_nonneg hV (mul_nonneg ha hb)))
    have hsqrt := Real.sq_sqrt (mul_nonneg hV hb)
    apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg ha (Real.sqrt_nonneg _))).mp
    rw [mul_pow, hsqrt]
    convert hsq using 1; ring
  have hkernel : ∀ {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
      (i : Fin d) (u : Lp ℂ 2 (reducedLaw Q)),
      ((u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        fun ω => (centeredClockField Q 0 ω : ℂ)) →
      ∀ (t : ℝ) (ht : 0 < t) (ζ : ℂ),
      ‖homogeneousGaussianEvolutionTimeDerivative Q i ζ u t‖ ≤
        (((d : ℝ) / (2 * t) + 4 / t + ‖ζ‖ ^ 2 * sourceReducedBound Λ / 2) *
          (4 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (2 * sourceReducedBound Λ * t * ‖ζ‖ ^ 2)) *
        Real.sqrt (clockVarianceConstant d Λ r *
          (((8 * Real.pi) ^ (-(d : ℝ) / 2) *
            Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * sourceReducedBound Λ ^ d)) *
              t ^ (-(d : ℝ) / 2))) := by
    intro d Λ r Q i u hu t ht ζ
    rw [homogeneousGaussianEvolutionTimeDerivative, dite_eq_left ht]
    change ‖complexClockSpatialPairing Q u
      (homogenizedGaussianKernelTimeDerivative Q i t ht ζ)‖ ≤ _
    have hc : Continuous (homogenizedGaussianKernelTimeDerivative Q i t ht ζ) := by
      unfold homogenizedGaussianKernelTimeDerivative homogenizedGaussianKernel
      fun_prop
    apply hdom Q u hu _ hc
      (integrable_homogenizedGaussianKernelTimeDerivative Q i t ht ζ)
      (anisotropicGaussian (homogenizedCoefficient Q) (4 * t))
      (integrable_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) _ (by positivity))
      (integral_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) _ (by positivity))
    · have hK : 0 < sourceReducedBound Λ := by
        unfold sourceReducedBound
        exact mul_pos (Real.exp_pos _)
          (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ])
      positivity
    · positivity
    · exact fun x => (hgauss Q t ht x).2
    · exact norm_homogenizedGaussianKernelTimeDerivative_le_four_time Q i t ht ζ
  intro d D
  let K := sourceReducedBound D.ellipticity
  let V := clockVarianceConstant d D.ellipticity D.dependenceRange
  let G := (8 * Real.pi) ^ (-(d : ℝ) / 2) *
    Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)
  let P := (d : ℝ) / 2 + 4 + K / 2
  let A := P * (4 : ℝ) ^ ((d : ℝ) / 2) * Real.sqrt (V * G)
  have hK : 0 < K := by
    dsimp [K, sourceReducedBound]
    exact mul_pos (Real.exp_pos _)
      (by nlinarith [D.one_le_ellipticity, sq_nonneg D.ellipticity])
  have hV : 0 ≤ V := by
    dsimp [V, clockVarianceConstant]
    have hr : 0 ≤ D.dependenceRange := by linarith [D.one_le_dependenceRange]
    positivity
  have hG : 0 ≤ G := by dsimp [G]; positivity
  have hP : 0 < P := by dsimp [P]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hrate (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (i : Fin d) (u : Lp ℂ 2 (reducedLaw Q))
      (hu : (u : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
        fun ω => (centeredClockField Q 0 ω : ℂ))
      (t : ℝ) (ht : 0 < t) (ζ : ℂ) :
      ‖homogeneousGaussianEvolutionTimeDerivative Q i ζ u t‖ ≤
        A * (t⁻¹ + ‖ζ‖ ^ 2) * Real.exp (2 * K * ‖ζ‖ ^ 2 * t) *
          t ^ (-(d : ℝ) / 4) := by
    have hsqrt : Real.sqrt (V * (G * t ^ (-(d : ℝ) / 2))) =
        Real.sqrt (V * G) * t ^ (-(d : ℝ) / 4) := by
      rw [← mul_assoc, Real.sqrt_mul (mul_nonneg hV hG), Real.sqrt_eq_rpow (t ^ (-(d : ℝ) / 2)),
        ← Real.rpow_mul ht.le]
      congr 2
      ring
    have hp : (d : ℝ) / (2 * t) + 4 / t + ‖ζ‖ ^ 2 * K / 2 ≤
        P * (t⁻¹ + ‖ζ‖ ^ 2) := by
      dsimp only [P]
      have h₁ : 0 ≤ ((d : ℝ) / 2 + 4) * ‖ζ‖ ^ 2 := by positivity
      have h₂ : 0 ≤ K / 2 * t⁻¹ := by positivity
      simp only [div_eq_mul_inv, mul_inv_rev] at *
      nlinarith only [h₁, h₂]
    have h := hkernel Q i u hu t ht ζ
    change _ ≤ (_ * (4 : ℝ) ^ ((d : ℝ) / 2) *
      Real.exp (2 * K * t * ‖ζ‖ ^ 2)) * Real.sqrt (V * (G * t ^ (-(d : ℝ) / 2))) at h
    rw [hsqrt] at h
    calc
      _ ≤ _ := h
      _ ≤ _ := by
        dsimp only [A]
        have he : 2 * K * t * ‖ζ‖ ^ 2 = 2 * K * ‖ζ‖ ^ 2 * t := by ring
        rw [he]
        calc
          _ ≤ (P * (t⁻¹ + ‖ζ‖ ^ 2) * (4 : ℝ) ^ ((d : ℝ) / 2) *
              Real.exp (2 * K * ‖ζ‖ ^ 2 * t)) *
              (Real.sqrt (V * G) * t ^ (-(d : ℝ) / 4)) := by
            gcongr
          _ = _ := by ring
  let C := A + 2 * K + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, hC, ?_⟩
  intro Q hQ μ hμ i ζ t ht
  have hu : (centeredComplexLp Q μ : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (centeredClockField Q 0 ω : ℂ) := by
    have hi : (∫ ω, μ ω ∂reducedLaw Q) =
        ((∫ ω : FieldPair d, ω.2 0 ∂reducedLaw Q : ℝ) : ℂ) := by
      rw [integral_congr_ae hμ, integral_complex_ofReal]
    filter_upwards [coeFn_centeredComplexLp Q μ, hμ] with ω h₁ h₂
    rw [h₁, h₂, hi]
    simp only [centeredClockField, Complex.ofReal_sub]
  refine (hrate Q i (centeredComplexLp Q μ) hu t ht ζ).trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg ht.le _)
  have hcoef : A * (t⁻¹ + ‖ζ‖ ^ 2) ≤ C * (t⁻¹ + ‖ζ‖ ^ 2) :=
    mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith)
      (add_nonneg (inv_nonneg.mpr ht.le) (sq_nonneg _))
  have hexp : Real.exp (2 * K * ‖ζ‖ ^ 2 * t) ≤ Real.exp (C * ‖ζ‖ ^ 2 * t) := by
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (by dsimp only [C]; linarith) (sq_nonneg ‖ζ‖)) ht.le
  exact mul_le_mul hcoef hexp (Real.exp_pos _).le (mul_nonneg hC.le (by positivity))

end EinsteinFull.Blueprint
