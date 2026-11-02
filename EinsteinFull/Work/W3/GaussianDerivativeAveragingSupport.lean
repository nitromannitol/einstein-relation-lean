import EinsteinFull.Work.W3.GaussianSchwartzBoundsSupport
import EinsteinFull.Calculus.SchwartzAverageSupport
import EinsteinFull.Calculus.FiniteTimeIntegralSupport
import EinsteinFull.Frozen.GaussianDerivativeAverage

/-!
# Genuine derivative tests and finite-time Gaussian averaging

Unforced kernels at every positive time are spatial dilations of the proved
time-one Schwartz kernel. Every fixed coordinate derivative is therefore an
actual Schwartz test. Its translated reduced-L2 Bochner integral is bounded
and commutes with the literal finite-time corrector integral.
-/

open MeasureTheory
open scoped BigOperators NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

/-- Exact spatial scaling of the unforced, fully anisotropic frozen kernel. -/
theorem homogenizedGaussianKernel_zero_scale (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (x : Vec d) :
    homogenizedGaussianKernel Q i s hs 0 x =
      (s ^ (-(d : ℝ) / 2) : ℝ) •
        homogenizedGaussianKernel Q i 1 zero_lt_one 0 ((Real.sqrt s)⁻¹ • x) := by
  have hq : (∑ j, ∑ k, ((Real.sqrt s)⁻¹ • x) j *
      ((homogenizedCoefficient Q)⁻¹) j k * ((Real.sqrt s)⁻¹ • x) k) =
      (Real.sqrt s)⁻¹ ^ 2 * (∑ j, ∑ k,
        x j * ((homogenizedCoefficient Q)⁻¹) j k * x k) := by
    simp only [Finset.mul_sum, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [inv_pow, Real.sq_sqrt hs.le] at hq
  rw [homogenizedGaussianKernel_zero_eq_ofReal, homogenizedGaussianKernel_zero_eq_ofReal,
    Complex.real_smul, ← Complex.ofReal_mul]
  apply congrArg Complex.ofReal
  unfold anisotropicGaussian
  rw [hq, mul_one, Real.mul_rpow (mul_pos (by norm_num) Real.pi_pos).le hs.le]
  have hexp (a : ℝ) : -(s⁻¹ * a) / (2 * 1) = -a / (2 * s) := by
    field_simp
  rw [hexp]
  change _ = s ^ (-(d : ℝ) / 2) * _
  ring

private def spatialDilation (a : ℝ) (ha : a ≠ 0) : Vec d ≃L[ℝ] Vec d where
  toLinearEquiv := LinearEquiv.smulOfNeZero ℝ (Vec d) a ha
  continuous_toFun := continuous_const.smul continuous_id
  continuous_invFun := continuous_const.smul continuous_id

/-- The literal unforced kernel is a Schwartz function at every positive time. -/
def unforcedGaussianSchwartz (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) : SchwartzMap (Vec d) ℂ :=
  (s ^ (-(d : ℝ) / 2) : ℝ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ
      (spatialDilation ((Real.sqrt s)⁻¹) (inv_ne_zero (Real.sqrt_pos.mpr hs).ne'))
      (homogenizedGaussianSchwartz Q i 1 zero_lt_one (by norm_num) le_rfl 0)

@[simp] theorem unforcedGaussianSchwartz_apply (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (x : Vec d) :
    unforcedGaussianSchwartz Q i s hs x = homogenizedGaussianKernel Q i s hs 0 x :=
  (homogenizedGaussianKernel_zero_scale Q i s hs x).symm

/-- Every fixed coordinate derivative is an actual Schwartz test, at every positive time. -/
def unforcedGaussianDerivativeSchwartz (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d) :
    SchwartzMap (Vec d) ℂ :=
  LineDeriv.iteratedLineDerivOp (fun j => unitVector (dirs j))
    (unforcedGaussianSchwartz Q i s hs)

@[simp] theorem unforcedGaussianDerivativeSchwartz_apply (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d) (x : Vec d) :
    unforcedGaussianDerivativeSchwartz Q i s hs k dirs x =
      iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs 0) x
        (fun j => unitVector (dirs j)) := by
  rw [unforcedGaussianDerivativeSchwartz, SchwartzMap.iteratedLineDerivOp_eq_iteratedFDeriv]
  have he : (unforcedGaussianSchwartz Q i s hs : Vec d → ℂ) =
      homogenizedGaussianKernel Q i s hs 0 := funext (unforcedGaussianSchwartz_apply Q i s hs)
  rw [he]

/-- Integrability of every frozen derivative kernel, with the required argument `-x`. -/
theorem integrable_gaussianDerivativeKernel (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d) :
    Integrable (fun x : Vec d => iteratedFDeriv ℝ k
      (homogenizedGaussianKernel Q i s hs 0) (-x) (fun j => unitVector (dirs j))) := by
  simpa only [unforcedGaussianDerivativeSchwartz_apply] using
    (unforcedGaussianDerivativeSchwartz Q i s hs k dirs).integrable.comp_neg

/-- Continuity of the same literal reflected derivative kernel. -/
theorem continuous_gaussianDerivativeKernel (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d) :
    Continuous (fun x : Vec d => iteratedFDeriv ℝ k
      (homogenizedGaussianKernel Q i s hs 0) (-x) (fun j => unitVector (dirs j))) := by
  have hc := (unforcedGaussianDerivativeSchwartz Q i s hs k dirs).continuous.comp continuous_neg
  change Continuous (fun x => unforcedGaussianDerivativeSchwartz Q i s hs k dirs (-x)) at hc
  simpa only [unforcedGaussianDerivativeSchwartz_apply] using hc

/-- The actual stationary convolution satisfies the scalar-kernel `L¹` bound. -/
theorem norm_stationarySchwartzAverage_le (Q : EnvironmentLaw d Λ₀ r₀)
    (ψ : SchwartzMap (Vec d) ℂ) (F : Lp ℂ 2 (reducedLaw Q)) :
    ‖stationarySchwartzAverage Q ψ F‖ ≤ (∫ x : Vec d, ‖ψ x‖) * ‖F‖ := by
  calc
    _ ≤ ∫ x : Vec d, ‖ψ (-x) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      simp_rw [norm_smul, LinearIsometry.norm_map]
      rw [integral_mul_const]
      exact congrArg (fun a : ℝ => a * ‖F‖)
        (integral_neg_eq_self (fun x : Vec d => ‖ψ x‖) volume)

/-- Stationary Schwartz averaging as the actual bounded linear map on reduced `L²`. -/
def stationarySchwartzAverageCLM (Q : EnvironmentLaw d Λ₀ r₀)
    (ψ : SchwartzMap (Vec d) ℂ) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  LinearMap.mkContinuous
    { toFun := stationarySchwartzAverage Q ψ
      map_add' := by
        intro F G
        unfold stationarySchwartzAverage
        simp_rw [map_add, smul_add]
        exact integral_add (integrable_stationarySchwartzAverage_integrand Q ψ F)
          (integrable_stationarySchwartzAverage_integrand Q ψ G)
      map_smul' := by
        intro c F
        unfold stationarySchwartzAverage
        simp_rw [map_smul, smul_comm (ψ (-_)) c]
        exact integral_smul c _ }
    (∫ x : Vec d, ‖ψ x‖) (norm_stationarySchwartzAverage_le Q ψ)

@[simp] theorem stationarySchwartzAverageCLM_apply (Q : EnvironmentLaw d Λ₀ r₀)
    (ψ : SchwartzMap (Vec d) ℂ) (F : Lp ℂ 2 (reducedLaw Q)) :
    stationarySchwartzAverageCLM Q ψ F = stationarySchwartzAverage Q ψ F := rfl

/-- Integrability of the literal random-field derivative-average integrand. -/
theorem integrable_gaussianDerivativeAverage_integrand (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (F : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun x : Vec d => iteratedFDeriv ℝ k
      (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0) (-x)
        (fun j => unitVector (dirs j)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F) := by
  simpa only [unforcedGaussianDerivativeSchwartz_apply] using
    integrable_stationarySchwartzAverage_integrand Q
      (unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩ s hs k dirs) F

/-- A bounded operator realizing exactly the frozen Gaussian derivative average. -/
def gaussianDerivativeAverageCLM (hd : 2 ≤ d) (Q : EnvironmentLaw d Λ₀ r₀)
    (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  stationarySchwartzAverageCLM Q
    (unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩ s hs k dirs)

@[simp] theorem gaussianDerivativeAverageCLM_apply (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (F : Lp ℂ 2 (reducedLaw Q)) :
    gaussianDerivativeAverageCLM hd Q s hs k dirs F =
      gaussianDerivativeAverage hd Q s hs k dirs F := by
  simp only [gaussianDerivativeAverageCLM, stationarySchwartzAverageCLM_apply,
    stationarySchwartzAverage, gaussianDerivativeAverage,
    unforcedGaussianDerivativeSchwartz_apply]

/-- The literal derivative average is controlled by the actual derivative kernel's `L¹` norm. -/
theorem norm_gaussianDerivativeAverage_le (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (F : Lp ℂ 2 (reducedLaw Q)) :
    ‖gaussianDerivativeAverage hd Q s hs k dirs F‖ ≤
      (∫ x : Vec d, ‖iteratedFDeriv ℝ k
        (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0) x
          (fun j => unitVector (dirs j))‖) * ‖F‖ := by
  simpa only [← gaussianDerivativeAverageCLM_apply, gaussianDerivativeAverageCLM,
    stationarySchwartzAverageCLM_apply, unforcedGaussianDerivativeSchwartz_apply] using
    norm_stationarySchwartzAverage_le Q
      (unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩ s hs k dirs) F

/-- Gaussian derivatives commute with the actual finite-time corrector integral. -/
theorem gaussianDerivativeAverage_finiteTimeCorrector (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (τ : ℝ≥0) (j : Fin d)
    (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d) :
    gaussianDerivativeAverage hd Q s hs k dirs
        (finiteTimeCorrector Q P hP.2.2.1 β τ j) =
      ∫ r in Set.Icc (0 : ℝ) (τ : ℝ),
        gaussianDerivativeAverage hd Q s hs k dirs (P r.toNNReal (β j)) := by
  simp only [← gaussianDerivativeAverageCLM_apply]
  exact ((gaussianDerivativeAverageCLM hd Q s hs k dirs).integral_comp_comm
    (integrableOn_finiteTimeCorrector_integrand Q i P hP β τ j)).symm

end EinsteinFull
