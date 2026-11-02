import EinsteinFull.Work.W3.GaussianJointProfileTestSupport
import EinsteinFull.Work.W3.GaussianProfileScalingSupport
import EinsteinFull.Calculus.SpatialPairingSupport
import EinsteinFull.Frozen.ModelTransposeEndpoint
import EinsteinFull.Frozen.ModelVelocityEndpoint
import EinsteinFull.Frozen.ModelClockEndpoint
import EinsteinFull.Frozen.JointCovariance

/-!
# Exact scaling of the actual Gaussian model endpoints

Adapted from W3/GaussianProfileProof at 06390cf78ded329afb93464b5066782b21f4ec10;
the unused late-propagation import is removed. No endpoint comparison estimate
is required for these exact identities.

The vector tests below use the literal anisotropic kernels and the joint index
carrier of `IsJointCovariance`. Their spatial covariance gives the frozen
profiles. Quantitative stochastic comparison errors are separate obligations.
-/

noncomputable section

namespace EinsteinFull

open EinsteinRelation MeasureTheory Filter
open scoped BigOperators Topology NNReal

variable {d : ℕ} {Λ₀ r₀ : ℝ}

private lemma scaledJointPairing_sum {ι : Type*} [Fintype ι]
    (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F : ι → SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    scaledJointPairing Q R hR Z (∑ j, F j) = ∑ j, scaledJointPairing Q R hR Z (F j) := by
  classical
  induction Finset.univ (α := ι) using Finset.induction_on with
  | empty => simp [scaledJointPairing]
  | @insert j s hj ih => rw [Finset.sum_insert hj, scaledJointPairing_add, ih, Finset.sum_insert hj]

/-- The backward-kernel convention contributes a minus sign to each derivative. -/
theorem fderiv_homogenizedGaussianKernel_neg_force_neg (Q : EnvironmentLaw d Λ₀ r₀)
    (i j : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) (x : Vec d) :
    fderiv ℝ (homogenizedGaussianKernel Q i s hs (-ζ)) (-x) (unitVector j) =
      -fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x (unitVector j) := by
  rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate,
    fderiv_homogenizedGaussianKernel_complexForce_coordinate,
    homogenizedGaussianKernel_neg_force]
  simp only [neg_neg, Matrix.mulVec_neg, Pi.neg_apply, Complex.ofReal_neg]
  ring

private lemma homogeneousDerivativeAverage_one (Q : EnvironmentLaw d Λ₀ r₀)
    (i j : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) (F : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousDerivativeAverage Q i s hs ζ 1 (fun _ => j) F =
      -(∫ x : Vec d, fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x
        (unitVector j) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F) := by
  simp only [homogeneousDerivativeAverage, iteratedFDeriv_one_apply,
    fderiv_homogenizedGaussianKernel_neg_force_neg, neg_smul, integral_neg]

/-- The normalized transpose endpoint is an actual joint Schwartz pairing. -/
theorem modelTransposeEndpoint_eq_profileTest (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ) :
    modelTransposeEndpoint hd Q Z (1 / 2) (by norm_num) ζ =
      scaledJointPairing Q 1 zero_lt_one Z (profileTransposeTest hd Q ζ) := by
  simp only [modelTransposeEndpoint, profileTransposeTest, scaledJointPairing_smul,
    scaledJointPairing_sum, scaledJointPairing_jointCoordinateSchwartz,
    homogeneousDerivativeAverage_one, profileGaussianDerivativeSchwartz_apply,
    inv_one, one_smul, Real.one_rpow, Complex.ofReal_one, Finset.sum_neg_distrib]
  simp only [neg_smul, neg_div, smul_neg]

/-- The normalized velocity endpoint retains its divergence and signed force terms. -/
theorem modelVelocityEndpoint_eq_profileTest (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) (i : Fin d) (ζ : ℂ) :
    modelVelocityEndpoint hd Q Z i (1 / 2) (by norm_num) ζ =
      scaledJointPairing Q 1 zero_lt_one Z (profileVelocityTest hd Q i ζ) := by
  simp only [modelVelocityEndpoint, profileVelocityTest, scaledJointPairing_add,
    scaledJointPairing_smul, scaledJointPairing_sum, scaledJointPairing_jointCoordinateSchwartz,
    homogeneousDerivativeAverage_one, profileGaussianDerivativeSchwartz_apply,
    profileGaussianSchwartz_apply, inv_one, one_smul, Real.one_rpow,
    Complex.ofReal_one, Finset.sum_neg_distrib, homogeneousAverage]
  simp only [neg_smul, neg_div, smul_neg]

/-- The normalized clock endpoint is the clock-coordinate Schwartz pairing. -/
theorem modelClockEndpoint_eq_profileTest (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) (ζ : ℂ) :
    modelClockEndpoint hd Q Z (1 / 2) (by norm_num) ζ =
      scaledJointPairing Q 1 zero_lt_one Z (profileClockTest hd Q ζ) := by
  simp only [modelClockEndpoint, profileClockTest, scaledJointPairing_smul,
    scaledJointPairing_jointCoordinateSchwartz, profileGaussianSchwartz_apply,
    inv_one, one_smul, Real.one_rpow, Complex.ofReal_one, homogeneousAverage]

/-- Literal homogeneous averaging under parabolic spatial scaling. -/
theorem homogeneousAverage_parabolic_scale (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (R s : ℝ) (hR : 0 < R) (hs : 0 < s) (ζ : ℂ)
    (F : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousAverage Q i (R ^ 2 * s) (mul_pos (sq_pos_of_pos hR) hs) ζ F =
      ((R ^ (-(d : ℝ)) : ℝ) : ℂ) •
        ∫ x : Vec d, homogenizedGaussianKernel Q i s hs (ζ * (R : ℂ)) (R⁻¹ • x) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F := by
  simp only [homogeneousAverage, homogenizedGaussianKernel_parabolic_scale Q i R s hR hs,
    Complex.real_smul, mul_smul, integral_smul]

private lemma homogeneousDerivativeAverage_parabolic_scale (Q : EnvironmentLaw d Λ₀ r₀)
    (i j : Fin d) (R s : ℝ) (hR : 0 < R) (hs : 0 < s) (ζ : ℂ)
    (F : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousDerivativeAverage Q i (R ^ 2 * s) (mul_pos (sq_pos_of_pos hR) hs)
      ζ 1 (fun _ => j) F =
      -(((R ^ (-(d : ℝ)) / R : ℝ) : ℂ) •
        ∫ x : Vec d, fderiv ℝ (homogenizedGaussianKernel Q i s hs (ζ * (R : ℂ)))
          (R⁻¹ • x) (unitVector j) •
          complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F) := by
  simp only [homogeneousDerivativeAverage_one,
    fderiv_homogenizedGaussianKernel_parabolic_scale Q i j R s hR hs,
    mul_smul, integral_smul]

private lemma profile_scale_factor (R : ℝ) (hR : 0 < R) :
    R ^ (-1 - (d : ℝ) / 2) * R ^ (-(d : ℝ) / 2) = R ^ (-(d : ℝ)) / R := by
  rw [← Real.rpow_add hR, ← Real.rpow_sub_one hR.ne']
  congr 1
  ring

private lemma profile_scale_force_factor (R : ℝ) (hR : 0 < R) (ζ : ℂ) :
    ζ * ((R ^ (-(d : ℝ)) : ℝ) : ℂ) =
      ((R ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) *
        (ζ * (R : ℂ) * ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ)) := by
  have h := congrArg Complex.ofReal (profile_scale_factor (d := d) R hR)
  simp only [Complex.ofReal_mul, Complex.ofReal_div] at h
  calc
    _ = ζ * (((R ^ (-(d : ℝ)) : ℝ) : ℂ) / (R : ℂ) * (R : ℂ)) := by
      rw [div_mul_cancel₀ _ (Complex.ofReal_ne_zero.mpr hR.ne')]
    _ = _ := by rw [← h]; ring

/-- The arbitrary-scale transpose endpoint is exactly `R^(-1-d/2) Z_R(F_z)`. -/
theorem modelTransposeEndpoint_eq_scaled_profileTest (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (R : ℝ) (hR : 0 < R) (ζ : ℂ) :
    modelTransposeEndpoint hd Q Z (R ^ 2 / 2) (by positivity) ζ =
      ((R ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) •
        scaledJointPairing Q R hR Z (profileTransposeTest hd Q (ζ * (R : ℂ))) := by
  simp only [show R ^ 2 / 2 = R ^ 2 * (1 / 2) by ring]
  simp only [modelTransposeEndpoint,
    homogeneousDerivativeAverage_parabolic_scale (s := 1 / 2) (hR := hR) (hs := by norm_num),
    profileTransposeTest, scaledJointPairing_smul, scaledJointPairing_sum,
    scaledJointPairing_jointCoordinateSchwartz, profileGaussianDerivativeSchwartz_apply,
    neg_mul, Finset.sum_neg_distrib, smul_neg, ← Finset.smul_sum, smul_smul]
  have h := congrArg Complex.ofReal (profile_scale_factor (d := d) R hR)
  simp only [Complex.ofReal_mul] at h
  rw [← h]
  module

/-- The velocity model has the same exact factor, including its signed force term. -/
theorem modelVelocityEndpoint_eq_scaled_profileTest (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (i : Fin d) (R : ℝ) (hR : 0 < R) (ζ : ℂ) :
    modelVelocityEndpoint hd Q Z i (R ^ 2 / 2) (by positivity) ζ =
      ((R ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) •
        scaledJointPairing Q R hR Z (profileVelocityTest hd Q i (ζ * (R : ℂ))) := by
  simp only [show R ^ 2 / 2 = R ^ 2 * (1 / 2) by ring]
  simp only [modelVelocityEndpoint,
    homogeneousDerivativeAverage_parabolic_scale (s := 1 / 2) (hR := hR) (hs := by norm_num),
    homogeneousAverage_parabolic_scale (s := 1 / 2) (hR := hR) (hs := by norm_num),
    profileVelocityTest, scaledJointPairing_add,
    scaledJointPairing_smul, scaledJointPairing_sum, scaledJointPairing_jointCoordinateSchwartz,
    profileGaussianDerivativeSchwartz_apply, profileGaussianSchwartz_apply,
    Finset.sum_neg_distrib, smul_neg, ← Finset.smul_sum, smul_add, smul_smul]
  have h := congrArg Complex.ofReal (profile_scale_factor (d := d) R hR)
  simp only [Complex.ofReal_mul] at h
  rw [← h, profile_scale_force_factor R hR ζ]
  module

/-- Exact clock scaling uses the same clock coordinate and no covariance premise. -/
theorem modelClockEndpoint_eq_scaled_profileTest (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (R : ℝ) (hR : 0 < R) (ζ : ℂ) :
    modelClockEndpoint hd Q Z (R ^ 2 / 2) (by positivity) ζ =
      ((R ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) •
        scaledJointPairing Q R hR Z (profileClockTest hd Q (ζ * (R : ℂ))) := by
  simp only [show R ^ 2 / 2 = R ^ 2 * (1 / 2) by ring]
  simp only [modelClockEndpoint,
    homogeneousAverage_parabolic_scale (s := 1 / 2) (hR := hR) (hs := by norm_num), profileClockTest,
    scaledJointPairing_smul, scaledJointPairing_jointCoordinateSchwartz,
    profileGaussianSchwartz_apply, smul_smul]
  rw [profile_scale_force_factor R hR ζ]

private lemma integral_smul_mul_smul (Q : EnvironmentLaw d Λ₀ r₀)
    (c : ℂ) (f g : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, (c • f) ω * (c • g) ω ∂reducedLaw Q) =
      (c * c) * ∫ ω, f ω * g ω ∂reducedLaw Q := by
  calc
    _ = ∫ ω, (c * c) * (f ω * g ω) ∂reducedLaw Q := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_smul c f, Lp.coeFn_smul c g] with ω hf hg
      rw [hf, hg]
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    _ = _ := integral_const_mul _ _

private lemma profile_product_scale (R : ℝ) (hR : 0 < R) :
    ((R ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) *
        ((R ^ (-1 - (d : ℝ) / 2) : ℝ) : ℂ) =
      ((R ^ (-(d : ℝ) - 2) : ℝ) : ℂ) := by
  rw [← Complex.ofReal_mul, ← Real.rpow_add hR]
  congr 2
  ring

/-- The actual bilinear model velocity moment has exactly the covariance scale
`R^(-d-2)`, with no quantitative covariance or endpoint-comparison premise. -/
theorem integral_modelTranspose_mul_velocity_eq_scaled_jointPairing (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (i : Fin d) (R : ℝ) (hR : 0 < R) (ζ : ℂ) :
    (∫ ω, modelTransposeEndpoint hd Q Z (R ^ 2 / 2) (by positivity) ζ ω *
      modelVelocityEndpoint hd Q Z i (R ^ 2 / 2) (by positivity) ζ ω ∂reducedLaw Q) =
      ((R ^ (-(d : ℝ) - 2) : ℝ) : ℂ) *
        ∫ ω, scaledJointPairing Q R hR Z (profileTransposeTest hd Q (ζ * (R : ℂ))) ω *
          scaledJointPairing Q R hR Z (profileVelocityTest hd Q i (ζ * (R : ℂ))) ω
          ∂reducedLaw Q := by
  rw [modelTransposeEndpoint_eq_scaled_profileTest hd Q Z R hR ζ,
    modelVelocityEndpoint_eq_scaled_profileTest hd Q Z i R hR ζ,
    integral_smul_mul_smul, profile_product_scale R hR]

/-- The clock model moment has the same exact covariance scale, retaining the
commutator-clock coordinate and the external signed complex force. -/
theorem integral_modelTranspose_mul_clock_eq_scaled_jointPairing (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (R : ℝ) (hR : 0 < R) (ζ : ℂ) :
    (∫ ω, modelTransposeEndpoint hd Q Z (R ^ 2 / 2) (by positivity) ζ ω *
      modelClockEndpoint hd Q Z (R ^ 2 / 2) (by positivity) ζ ω ∂reducedLaw Q) =
      ((R ^ (-(d : ℝ) - 2) : ℝ) : ℂ) *
        ∫ ω, scaledJointPairing Q R hR Z (profileTransposeTest hd Q (ζ * (R : ℂ))) ω *
          scaledJointPairing Q R hR Z (profileClockTest hd Q (ζ * (R : ℂ))) ω
          ∂reducedLaw Q := by
  rw [modelTransposeEndpoint_eq_scaled_profileTest hd Q Z R hR ζ,
    modelClockEndpoint_eq_scaled_profileTest hd Q Z R hR ζ,
    integral_smul_mul_smul, profile_product_scale R hR]

end EinsteinFull
