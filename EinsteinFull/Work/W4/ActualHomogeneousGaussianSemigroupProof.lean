import EinsteinFull.Work.W3.GaussianSchwartzBoundsSupport
import EinsteinFull.Calculus.SpatialPairingSupport
import EinsteinFull.Calculus.ComplexHorizontalIntegrationSupport
import EinsteinFull.Frozen.HomogeneousAverage
import EinsteinFull.Frozen.ComplexTransposeSemigroup
import Mathlib.Analysis.Convolution

/-!
The actual stationary Gaussian integral. The covariance is the literal
homogenized matrix, and the force is complex and signed throughout.
-/

open MeasureTheory Filter
open scoped Topology
open scoped NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ r : ℝ}

private theorem gaussianReducedBound_pos (Q : EnvironmentLaw d Λ r) :
    0 < sourceReducedBound Λ := by
  unfold sourceReducedBound
  exact mul_pos (Real.exp_pos _) (by nlinarith [Q.ellipticity_parameter, sq_nonneg Λ])

private theorem gaussianEuclideanNorm_sq (x : Vec d) : euclideanNorm x ^ 2 = euclideanSq x := by
  apply Real.sq_sqrt
  unfold euclideanSq dot
  exact Finset.sum_nonneg fun j _ => mul_self_nonneg (x j)

private theorem gaussianCoord_le_euclideanNorm (x : Vec d) (j : Fin d) :
    |x j| ≤ euclideanNorm x := by
  apply le_of_sq_le_sq _ (Real.sqrt_nonneg _)
  change |x j| ^ 2 ≤ euclideanNorm x ^ 2
  rw [sq_abs, gaussianEuclideanNorm_sq]
  simpa only [euclideanSq, dot, pow_two] using
    Finset.single_le_sum (fun k _ => mul_self_nonneg (x k)) (Finset.mem_univ j)


/-- Exact absolute value: only the imaginary force produces norm growth. -/
theorem norm_homogenizedGaussianKernel_eq_realForce
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (x : Vec d) :
    ‖homogenizedGaussianKernel Q i s hs ζ x‖ =
      Real.exp (ζ.im ^ 2 * s * homogenizedCoefficient Q i i / 2) *
        ‖homogenizedGaussianKernel Q i s hs (ζ.re : ℂ) x‖ := by
  rw [homogenizedGaussianKernel_eq_exp_tilt,
    homogenizedGaussianKernel_eq_exp_tilt, norm_mul, norm_mul,
    Complex.norm_exp, Complex.norm_exp, ← mul_assoc, ← Real.exp_add]
  congr 2
  simp only [pow_two, Complex.sub_re, Complex.mul_re, Complex.mul_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.div_ofNat_re]
  ring

/-- The full anisotropic real-force kernel is integrable on spatial Lebesgue measure. -/
theorem integrable_homogenizedGaussianKernel_realForce
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (a : ℝ) :
    Integrable (homogenizedGaussianKernel Q i s hs (a : ℂ)) := by
  change Integrable (fun x => homogenizedGaussianKernel Q i s hs (a : ℂ) x)
  simp_rw [homogenizedGaussianKernel_realForce_eq_translate,
    homogenizedGaussianKernel_zero_eq_ofReal]
  have h : Integrable (fun x : Vec d => (anisotropicGaussian (homogenizedCoefficient Q) s x : ℂ)) :=
    (integrable_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) s hs).ofReal
  exact h.comp_sub_right _

/-- The complex-force integral has a genuine Bochner integrable scalar kernel. -/
theorem integrable_homogenizedGaussianKernel
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    Integrable (homogenizedGaussianKernel Q i s hs ζ) := by
  have hc : Continuous (homogenizedGaussianKernel Q i s hs ζ) := by
    unfold homogenizedGaussianKernel
    fun_prop
  apply Integrable.mono' ((integrable_homogenizedGaussianKernel_realForce Q i s hs
    ζ.re).norm.const_mul (Real.exp (ζ.im ^ 2 * s * homogenizedCoefficient Q i i / 2)))
    hc.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun x =>
    (norm_homogenizedGaussianKernel_eq_realForce Q i s hs ζ x).le

/-- The literal stationary convolution is Bochner integrable for every L2 datum. -/
theorem integrable_homogeneousAverage_integrand
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun x : Vec d => homogenizedGaussianKernel Q i s hs ζ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) := by
  letI := reducedLaw_probability Q
  apply integrable_kernel_complexTranslation _ _ _
    (integrable_homogenizedGaussianKernel Q i s hs ζ)
  unfold homogenizedGaussianKernel
  fun_prop

/-- Exact spatial L1 norm, with the actual diagonal homogenized coefficient. -/
theorem integral_norm_homogenizedGaussianKernel
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    (∫ x : Vec d, ‖homogenizedGaussianKernel Q i s hs ζ x‖) =
      Real.exp (ζ.im ^ 2 * s * homogenizedCoefficient Q i i / 2) := by
  conv_lhs =>
    arg 2
    ext x
    rw [norm_homogenizedGaussianKernel_eq_realForce]
  simp_rw [homogenizedGaussianKernel_realForce_eq_translate,
    homogenizedGaussianKernel_zero_eq_ofReal, Complex.norm_real, Real.norm_eq_abs]
  have hn (x : Vec d) : 0 ≤ anisotropicGaussian (homogenizedCoefficient Q) s x := by
    unfold anisotropicGaussian
    positivity
  simp_rw [abs_of_nonneg (hn _)]
  rw [integral_const_mul, integral_sub_right_eq_self,
    integral_anisotropicGaussian _ (posDef_homogenizedCoefficient Q) s hs, mul_one]

/-- Boundedness of the literal Gaussian integral, for every complex force and L2 datum. -/
theorem norm_homogeneousAverage_le
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖homogeneousAverage Q i s hs ζ f‖ ≤
      Real.exp (ζ.im ^ 2 * s * homogenizedCoefficient Q i i / 2) * ‖f‖ := by
  calc
    _ ≤ ∫ x : Vec d, ‖homogenizedGaussianKernel Q i s hs ζ x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f‖ :=
      norm_integral_le_integral_norm _
    _ = _ := by
      simp_rw [norm_smul, norm_complexTranslation]
      rw [integral_mul_const, integral_norm_homogenizedGaussianKernel]

/-- The frozen integral bundled as an actual bounded complex linear operator. -/
def homogeneousAverageCLM (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  LinearMap.mkContinuous
    { toFun := homogeneousAverage Q i s hs ζ
      map_add' := fun f g => by
        simp only [homogeneousAverage, map_add, smul_add]
        exact integral_add (integrable_homogeneousAverage_integrand Q i s hs ζ f)
          (integrable_homogeneousAverage_integrand Q i s hs ζ g)
      map_smul' := fun c f => by
        simp only [homogeneousAverage, map_smul, RingHom.id_apply, smul_comm _ c]
        exact integral_smul c _ }
    (Real.exp (ζ.im ^ 2 * s * homogenizedCoefficient Q i i / 2))
    (norm_homogeneousAverage_le Q i s hs ζ)

/-- Bundling preserves the exact frozen integral definition. -/
theorem homogeneousAverageCLM_apply (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousAverageCLM Q i s hs ζ f = homogeneousAverage Q i s hs ζ f := rfl

/-- Translation commutes with the actual Gaussian operator. -/
theorem complexTranslation_homogeneousAverage
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (x : Vec d) (f : Lp ℂ 2 (reducedLaw Q)) :
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
        (homogeneousAverage Q i s hs ζ f) =
      ∫ y : Vec d, homogenizedGaussianKernel Q i s hs ζ y •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (x + y) f := by
  change (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x).toContinuousLinearMap
    (∫ y : Vec d, homogenizedGaussianKernel Q i s hs ζ y •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y f) = _
  rw [← (complexTranslation _ _ x).toContinuousLinearMap.integral_comp_comm
    (integrable_homogeneousAverage_integrand Q i s hs ζ f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    simp only [LinearIsometry.coe_toContinuousLinearMap, map_smul, complexTranslation_add]

private theorem integrable_gaussian_translation_product
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun p : Vec d × Vec d =>
      (homogenizedGaussianKernel Q i s hs ζ p.1 * homogenizedGaussianKernel Q i t ht ζ p.2) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (p.1 + p.2) f)
      (volume.prod volume) := by
  letI := reducedLaw_probability Q
  have hK (a : ℝ) (ha : 0 < a) : Continuous (homogenizedGaussianKernel Q i a ha ζ) := by
    unfold homogenizedGaussianKernel
    fun_prop
  have hT : Continuous (fun p : Vec d × Vec d =>
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (p.1 + p.2) f) :=
    (continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
    ((continuous_fst.add continuous_snd).prodMk continuous_const)
  refine (((integrable_homogenizedGaussianKernel Q i s hs ζ).norm.mul_prod
    (integrable_homogenizedGaussianKernel Q i t ht ζ).norm).mul_const ‖f‖).mono'
    (((hK s hs).comp continuous_fst).mul ((hK t ht).comp continuous_snd) |>.smul hT
      |>.aestronglyMeasurable) ?_
  exact Filter.Eventually.of_forall fun p => by
    simp only [norm_smul, norm_mul, norm_complexTranslation, le_refl]

private theorem integrable_gaussian_translation_convolution
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun p : Vec d × Vec d =>
      (homogenizedGaussianKernel Q i s hs ζ (p.1 - p.2) * homogenizedGaussianKernel Q i t ht ζ p.2) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) p.1 f)
      (volume.prod volume) := by
  letI := reducedLaw_probability Q
  have hK (a : ℝ) (ha : 0 < a) : Continuous (homogenizedGaussianKernel Q i a ha ζ) := by
    unfold homogenizedGaussianKernel
    fun_prop
  have hT : Continuous (fun p : Vec d × Vec d =>
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) p.1 f) :=
    (continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
    (continuous_fst.prodMk continuous_const)
  have hb := ((integrable_homogenizedGaussianKernel Q i t ht ζ).norm.convolution_integrand
    (ContinuousLinearMap.mul ℝ ℝ) (integrable_homogenizedGaussianKernel Q i s hs ζ).norm
    ).mul_const ‖f‖
  apply hb.mono'
    (((hK s hs).comp (continuous_fst.sub continuous_snd)).fun_mul
      ((hK t ht).comp continuous_snd) |>.fun_smul hT |>.aestronglyMeasurable)
  exact Filter.Eventually.of_forall fun p => by
    simp only [Pi.smul_apply, Pi.mul_apply, Pi.sub_apply, Function.comp_apply, norm_smul, norm_mul, norm_complexTranslation, ContinuousLinearMap.mul_apply']
    exact le_of_eq (congrArg (fun a : ℝ => a * ‖f‖) (mul_comm _ _))

/-- Exact semigroup identity for the actual positive-time stationary Gaussian integrals. -/
theorem homogeneousAverage_add
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s t : ℝ) (hs : 0 < s) (ht : 0 < t)
    (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousAverage Q i s hs ζ (homogeneousAverage Q i t ht ζ f) =
      homogeneousAverage Q i (s + t) (add_pos hs ht) ζ f := by
  let K := fun (a : ℝ) (ha : 0 < a) => homogenizedGaussianKernel Q i a ha ζ
  let T := fun x => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f
  have hprod := integrable_gaussian_translation_product Q i s t hs ht ζ f
  have hconv := integrable_gaussian_translation_convolution Q i s t hs ht ζ f
  change Integrable (fun p : Vec d × Vec d => (K s hs p.1 * K t ht p.2) • T (p.1 + p.2))
    (volume.prod volume) at hprod
  change Integrable (fun p : Vec d × Vec d => (K s hs (p.1 - p.2) * K t ht p.2) • T p.1)
    (volume.prod volume) at hconv
  calc
    _ = ∫ x : Vec d, ∫ y : Vec d, (K s hs x * K t ht y) • T (x + y) := by
      change (∫ x : Vec d, K s hs x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
          (homogeneousAverage Q i t ht ζ f)) = _
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun x => ?_
      dsimp only
      rw [complexTranslation_homogeneousAverage, ← integral_smul]
      simp only [smul_smul, K, T]
    _ = ∫ y : Vec d, ∫ x : Vec d, (K s hs x * K t ht y) • T (x + y) :=
      integral_integral_swap hprod
    _ = ∫ y : Vec d, ∫ x : Vec d, (K s hs (x - y) * K t ht y) • T x := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun y => ?_
      simpa only [sub_add_cancel] using
        (integral_sub_right_eq_self (fun x => (K s hs x * K t ht y) • T (x + y)) y).symm
    _ = ∫ x : Vec d, ∫ y : Vec d, (K s hs (x - y) * K t ht y) • T x :=
      (integral_integral_swap hconv).symm
    _ = _ := by
      apply integral_congr_ae
      refine Filter.Eventually.of_forall fun x => ?_
      dsimp only [K, T]
      rw [integral_smul_const, integral_homogenizedGaussianKernel_convolution]

/-- A structural operator bound, uniform in the environment law. -/
theorem norm_homogeneousAverageCLM_le
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    ‖homogeneousAverageCLM Q i s hs ζ‖ ≤
      Real.exp (sourceReducedBound Λ * ‖ζ‖ ^ 2 * s / 2) := by
  have he : |homogenizedCoefficient Q i i| ≤ sourceReducedBound Λ := by
    have h := (gaussianCoord_le_euclideanNorm ((homogenizedCoefficient Q).mulVec
      (unitVector i)) i).trans (homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q i)
    simpa [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite] using h
  have hi : ζ.im ^ 2 ≤ ‖ζ‖ ^ 2 := by
    nlinarith only [Complex.sq_norm_sub_sq_im ζ, sq_nonneg ζ.re]
  apply (homogeneousAverageCLM Q i s hs ζ).opNorm_le_bound (Real.exp_pos _).le
  intro f
  exact (norm_homogeneousAverage_le Q i s hs ζ f).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by
      have h₁ := mul_le_mul_of_nonneg_left (le_abs_self _ |>.trans he)
        (mul_nonneg (sq_nonneg ζ.im) hs.le)
      have h₂ := mul_le_mul_of_nonneg_right hi (mul_nonneg (gaussianReducedBound_pos Q).le hs.le)
      nlinarith only [h₁, h₂])) (norm_nonneg f))

private def gaussianBilinearTest (Q : EnvironmentLaw d Λ r)
    (f : Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] ℂ :=
  innerSL ℂ (star f)

private theorem gaussianBilinearTest_apply (Q : EnvironmentLaw d Λ r)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    gaussianBilinearTest Q f g = ∫ ω, f ω * g ω ∂reducedLaw Q := by
  rw [gaussianBilinearTest, innerSL_apply_apply, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_star f] with ω hω
  change (star f) ω = star (f ω) at hω
  simp only [hω, RCLike.inner_apply, Complex.star_def, starRingEnd_self_apply]
  ring

private theorem gaussianBilinearTest_symm (Q : EnvironmentLaw d Λ r)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    gaussianBilinearTest Q f g = gaussianBilinearTest Q g f := by
  simp only [gaussianBilinearTest_apply, mul_comm]

private theorem gaussianBilinearTest_translation (Q : EnvironmentLaw d Λ r)
    (x : Vec d) (f g : Lp ℂ 2 (reducedLaw Q)) :
    gaussianBilinearTest Q g (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) =
      gaussianBilinearTest Q f (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (-x) g) := by
  rw [gaussianBilinearTest_symm Q f]
  change inner ℂ (star g) (complexTranslation _ _ x f) =
    inner ℂ (star (complexTranslation _ _ (-x) g)) f
  have h := (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x).inner_map_map
    (star (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (-x) g)) f
  rw [← complexTranslation_star, ← complexTranslation_add, add_neg_cancel,
    complexTranslation_zero, complexTranslation_star] at h
  exact h

/-- The actual homogeneous bilinear transpose reverses the signed complex force. -/
theorem integral_homogeneousAverage_bilinear_transpose
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (f g : Lp ℂ 2 (reducedLaw Q)) :
    (∫ ω, homogeneousAverage Q i s hs ζ f ω * g ω ∂reducedLaw Q) =
      ∫ ω, f ω * homogeneousAverage Q i s hs (-ζ) g ω ∂reducedLaw Q := by
  rw [← gaussianBilinearTest_apply, gaussianBilinearTest_symm Q _ g,
    ← gaussianBilinearTest_apply]
  change gaussianBilinearTest Q g (∫ x : Vec d, homogenizedGaussianKernel Q i s hs ζ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) =
    gaussianBilinearTest Q f (∫ x : Vec d, homogenizedGaussianKernel Q i s hs (-ζ) x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g)
  rw [← (gaussianBilinearTest Q g).integral_comp_comm
      (integrable_homogeneousAverage_integrand Q i s hs ζ f),
    ← (gaussianBilinearTest Q f).integral_comp_comm
      (integrable_homogeneousAverage_integrand Q i s hs (-ζ) g)]
  simp only [map_smul, smul_eq_mul]
  conv_lhs =>
    arg 2
    ext x
    rw [gaussianBilinearTest_translation]
  calc
    _ = ∫ x : Vec d, homogenizedGaussianKernel Q i s hs ζ (-x) *
        gaussianBilinearTest Q f (complexTranslation (reducedLaw Q)
          (reducedLaw_stationary Q) x g) := by
      simpa only [neg_neg] using
        (integral_neg_eq_self (fun x : Vec d => homogenizedGaussianKernel Q i s hs ζ x *
          gaussianBilinearTest Q f (complexTranslation (reducedLaw Q)
            (reducedLaw_stationary Q) (-x) g)) volume).symm
    _ = _ := by simp only [homogenizedGaussianKernel_neg_force]

/-- Actual Gaussian evolution including time zero. -/
def homogeneousGaussianEvolution (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (t : ℝ≥0) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  if ht : 0 < (t : ℝ) then homogeneousAverageCLM Q i t ht ζ else ContinuousLinearMap.id ℂ _

/-- The zero-time operator is exactly the identity. -/
theorem homogeneousGaussianEvolution_zero (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ) :
    homogeneousGaussianEvolution Q i ζ 0 = ContinuousLinearMap.id ℂ _ := by
  simp only [homogeneousGaussianEvolution, NNReal.coe_zero, lt_self_iff_false, ↓reduceDIte]

/-- At every positive time this is precisely the frozen Gaussian integral. -/
theorem homogeneousGaussianEvolution_pos (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousGaussianEvolution Q i ζ t f = homogeneousAverage Q i t ht ζ f := by
  simp only [homogeneousGaussianEvolution, dif_pos ht, homogeneousAverageCLM_apply]

/-- The exact operator semigroup law, including zero times. -/
theorem homogeneousGaussianEvolution_add (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (s t : ℝ≥0) :
    homogeneousGaussianEvolution Q i ζ (s + t) =
      (homogeneousGaussianEvolution Q i ζ s).comp (homogeneousGaussianEvolution Q i ζ t) := by
  by_cases hs : s = 0
  · subst s
    simp only [zero_add, homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_comp]
  by_cases ht : t = 0
  · subst t
    simp only [add_zero, homogeneousGaussianEvolution_zero, ContinuousLinearMap.comp_id]
  have hs' : 0 < (s : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hs)
  have ht' : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
  apply ContinuousLinearMap.ext
  intro f
  simp only [ContinuousLinearMap.comp_apply,
    homogeneousGaussianEvolution_pos Q i ζ s hs', homogeneousGaussianEvolution_pos Q i ζ t ht',
    homogeneousGaussianEvolution_pos Q i ζ (s + t) (add_pos hs' ht')]
  exact (homogeneousAverage_add Q i s t hs' ht' ζ f).symm

private theorem anisotropicGaussian_scale (A : Mat d) (c s : ℝ)
    (hc : 0 < c) (hs : 0 < s) (x : Vec d) :
    anisotropicGaussian A (c ^ 2 * s) (c • x) = (c ^ d)⁻¹ * anisotropicGaussian A s x := by
  have hq : (∑ j, ∑ k, (c • x) j * (A⁻¹) j k * (c • x) k) =
      c ^ 2 * ∑ j, ∑ k, x j * (A⁻¹) j k * x k := by
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hp : (c ^ 2) ^ (-(d : ℝ) / 2) = (c ^ d)⁻¹ := by
    rw [← Real.rpow_natCast c 2, ← Real.rpow_mul hc.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ) * (-(d : ℝ) / 2) = -(d : ℝ) by ring,
      Real.rpow_neg hc.le, Real.rpow_natCast]
  unfold anisotropicGaussian
  rw [hq, show 2 * Real.pi * (c ^ 2 * s) = c ^ 2 * (2 * Real.pi * s) by ring,
    Real.mul_rpow (sq_nonneg c) (by positivity), hp]
  have he (q : ℝ) : -(c ^ 2 * q) / (2 * (c ^ 2 * s)) = -q / (2 * s) := by
    field_simp
  rw [he]
  ring

/-- Parabolic scaling preserves both the covariance and the signed complex force. -/
theorem homogenizedGaussianKernel_scale (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (c s : ℝ) (hc : 0 < c) (hs : 0 < s) (ζ : ℂ) (x : Vec d) :
    homogenizedGaussianKernel Q i (c ^ 2 * s) (mul_pos (sq_pos_of_pos hc) hs) ζ (c • x) =
      (((c ^ d)⁻¹ : ℝ) : ℂ) * homogenizedGaussianKernel Q i s hs (ζ * (c : ℂ)) x := by
  rw [homogenizedGaussianKernel_eq_exp_tilt, homogenizedGaussianKernel_eq_exp_tilt,
    anisotropicGaussian_scale _ c s hc hs x]
  simp only [Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul, Complex.ofReal_pow]
  have he : ζ * ((c : ℂ) * (x i : ℂ)) - ζ ^ 2 * ((c : ℂ) ^ 2 * (s : ℂ)) *
      (homogenizedCoefficient Q i i : ℂ) / 2 =
      (ζ * (c : ℂ)) * (x i : ℂ) - (ζ * (c : ℂ)) ^ 2 * (s : ℂ) *
        (homogenizedCoefficient Q i i : ℂ) / 2 := by ring
  rw [he]
  ring

/-- A fixed unit-time Gaussian represents the actual operator after parabolic rescaling. -/
theorem homogeneousAverage_eq_scaled (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    homogeneousAverage Q i s hs ζ f =
      ∫ x : Vec d, homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (Real.sqrt s : ℂ)) x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (Real.sqrt s • x) f := by
  have hc : 0 < Real.sqrt s := Real.sqrt_pos.mpr hs
  have hscale (x : Vec d) :
      homogenizedGaussianKernel Q i s hs ζ (Real.sqrt s • x) =
        (((Real.sqrt s ^ d)⁻¹ : ℝ) : ℂ) *
          homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (Real.sqrt s : ℂ)) x := by
    simpa only [Real.sq_sqrt hs.le, mul_one] using
      homogenizedGaussianKernel_scale Q i (Real.sqrt s) 1 hc zero_lt_one ζ x
  have h := Measure.integral_comp_smul (volume : Measure (Vec d))
    (fun x => homogenizedGaussianKernel Q i s hs ζ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) (Real.sqrt s)
  simp only [Module.finrank_pi, Fintype.card_fin,
    abs_of_nonneg (inv_nonneg.mpr (pow_nonneg hc.le _))] at h
  simp only [hscale, mul_smul, ← Complex.coe_smul] at h
  rw [integral_smul] at h
  exact (smul_right_injective _ (inv_ne_zero (pow_ne_zero d hc.ne')) h).symm

private theorem integrable_gaussianEnvelope (K : ℝ) (hK : 0 < K) :
    Integrable (fun x : Vec d => Real.exp (-euclideanSq x / (4 * K))) := by
  have hg : Integrable (fun a : ℝ => Real.exp (-(a * a) / (4 * K))) := by
    convert integrable_exp_neg_mul_sq (b := 1 / (4 * K)) (by positivity) using 1
    ext a
    congr 1
    ring
  have hp : Integrable (fun x : Vec d => ∏ j, Real.exp (-(x j * x j) / (4 * K))) := by
    rw [volume_pi]
    simpa using! (Integrable.fintype_prod fun _ : Fin d => hg)
  convert hp using 1
  ext x
  rw [← Real.exp_sum]
  congr 1
  simp only [euclideanSq, dot, Finset.sum_div, Finset.sum_neg_distrib, neg_div]

/-- Strong continuity of the fixed-scale integral, including the zero spatial scale. -/
theorem continuous_scaled_homogeneousAverage (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun c : ℝ => ∫ x : Vec d,
      homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (c : ℂ)) x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (c • x) f) := by
  letI := reducedLaw_probability Q
  let K := sourceReducedBound Λ
  let P := Real.sqrt ((Fintype.card (Equiv.Perm (Fin d)) : ℝ) * K ^ d)
  have hK : 0 < K := gaussianReducedBound_pos Q
  have hP : 0 ≤ P := Real.sqrt_nonneg _
  have hspace (c : ℝ) : Continuous (fun x : Vec d =>
      homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (c : ℂ)) x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (c • x) f) := by
    have hk : Continuous (homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (c : ℂ))) := by
      exact (contDiff_homogenizedGaussianKernel_complexForce Q i 1 zero_lt_one
        (ζ * (c : ℂ))).continuous
    have ht : Continuous (fun x : Vec d =>
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (c • x) f) := by
      exact (continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
        (((continuous_const (y := c)).fun_smul (continuous_id (X := Vec d))).prodMk continuous_const)
    exact hk.fun_smul ht
  apply continuous_iff_continuousAt.mpr
  intro c₀
  let M := ‖ζ‖ * (|c₀| + 1)
  have hc : ∀ᶠ c : ℝ in 𝓝 c₀, |c| < |c₀| + 1 :=
    (continuous_abs.tendsto c₀).eventually (gt_mem_nhds (by linarith))
  apply continuousAt_of_dominated (Filter.Eventually.of_forall fun c =>
    (hspace c).aestronglyMeasurable)
    (bound := fun x : Vec d => (P * Real.exp (2 * K * M ^ 2) * ‖f‖) *
      Real.exp (-euclideanSq x / (4 * K)))
  · filter_upwards [hc] with c hc
    refine Filter.Eventually.of_forall fun x => ?_
    have hn : ‖ζ * (c : ℂ)‖ ≤ M := by
      simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left hc.le (norm_nonneg ζ)
    have hsq : ‖ζ * (c : ℂ)‖ ^ 2 ≤ M ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hn 2
    have hb := norm_homogenizedGaussianKernel_le_gaussian Q i 1 zero_lt_one
      (by norm_num) le_rfl (ζ * (c : ℂ)) x
    rw [norm_smul, norm_complexTranslation]
    calc
      _ ≤ (P * Real.exp (2 * K * ‖ζ * (c : ℂ)‖ ^ 2 -
          euclideanNorm x ^ 2 / (4 * K))) * ‖f‖ :=
        mul_le_mul_of_nonneg_right hb (norm_nonneg f)
      _ ≤ (P * Real.exp (2 * K * M ^ 2 - euclideanNorm x ^ 2 / (4 * K))) * ‖f‖ := by
        gcongr
      _ = _ := by rw [gaussianEuclideanNorm_sq, Real.exp_sub, neg_div, Real.exp_neg]; ring
  · exact (integrable_gaussianEnvelope K hK).const_mul _
  · refine Filter.Eventually.of_forall fun x => ?_
    have hk : Continuous (fun c : ℝ =>
        homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (c : ℂ)) x) := by
      unfold homogenizedGaussianKernel
      fun_prop
    exact (hk.fun_smul ((continuous_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)).comp
      ((continuous_id.fun_smul continuous_const).prodMk continuous_const))).continuousAt

/-- Strong continuity of the actual homogeneous Gaussian evolution at every nonnegative time. -/
theorem continuous_homogeneousGaussianEvolution (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t : ℝ≥0 => homogeneousGaussianEvolution Q i ζ t f) := by
  have he (t : ℝ≥0) : homogeneousGaussianEvolution Q i ζ t f =
      ∫ x : Vec d, homogenizedGaussianKernel Q i 1 zero_lt_one (ζ * (Real.sqrt t : ℂ)) x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (Real.sqrt t • x) f := by
    by_cases ht : t = 0
    · subst t
      simp only [homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_apply,
        NNReal.coe_zero, Real.sqrt_zero, Complex.ofReal_zero, mul_zero, zero_smul,
        complexTranslation_zero]
      rw [integral_smul_const]
      have hmass : (∫ x : Vec d, homogenizedGaussianKernel Q i 1 zero_lt_one 0 x) = 1 := by
        simp_rw [homogenizedGaussianKernel_zero_eq_ofReal]
        rw [integral_complex_ofReal, integral_anisotropicGaussian _
          (posDef_homogenizedCoefficient Q) 1 zero_lt_one, Complex.ofReal_one]
      rw [hmass, one_smul]
    · have ht' : 0 < (t : ℝ) := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr ht)
      rw [homogeneousGaussianEvolution_pos Q i ζ t ht', homogeneousAverage_eq_scaled]
  simp_rw [he]
  exact (continuous_scaled_homogeneousAverage Q i ζ f).comp
    (Real.continuous_sqrt.comp NNReal.continuous_coe)

/-- The structural complex-force growth bound also includes time zero. -/
theorem norm_homogeneousGaussianEvolution_le (Q : EnvironmentLaw d Λ r) (i : Fin d)
    (ζ : ℂ) (t : ℝ≥0) :
    ‖homogeneousGaussianEvolution Q i ζ t‖ ≤
      Real.exp (sourceReducedBound Λ * ‖ζ‖ ^ 2 * (t : ℝ) / 2) := by
  by_cases ht : 0 < (t : ℝ)
  · rw [homogeneousGaussianEvolution, dif_pos ht]
    exact norm_homogeneousAverageCLM_le Q i t ht ζ
  · have ht₀ : t = 0 := NNReal.coe_eq_zero.mp (le_antisymm (not_lt.mp ht) t.coe_nonneg)
    subst t
    simp only [homogeneousGaussianEvolution_zero, NNReal.coe_zero, mul_zero, zero_div, Real.exp_zero]
    exact ContinuousLinearMap.norm_id_le

/-- Real signed forces act by contractions at all nonnegative times. -/
theorem norm_homogeneousGaussianEvolution_realForce_apply_le (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (a : ℝ) (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖homogeneousGaussianEvolution Q i (a : ℂ) t f‖ ≤ ‖f‖ := by
  by_cases ht : 0 < (t : ℝ)
  · rw [homogeneousGaussianEvolution_pos Q i (a : ℂ) t ht]
    simpa only [Complex.ofReal_im, zero_pow two_ne_zero, zero_mul, zero_div,
      Real.exp_zero, one_mul] using norm_homogeneousAverage_le Q i t ht (a : ℂ) f
  · have ht₀ : t = 0 := NNReal.coe_eq_zero.mp (le_antisymm (not_lt.mp ht) t.coe_nonneg)
    subst t
    simp only [homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_apply, le_refl]

/-- The constructed all-time negative-force family is the exact bilinear transpose. -/
theorem isComplexTransposeSemigroup_homogeneousGaussianEvolution (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (ζ : ℂ) :
    IsComplexTransposeSemigroup Q (homogeneousGaussianEvolution Q i ζ)
      (homogeneousGaussianEvolution Q i (-ζ)) := by
  intro t f g
  by_cases ht : 0 < (t : ℝ)
  · simp only [homogeneousGaussianEvolution_pos Q i ζ t ht,
      homogeneousGaussianEvolution_pos Q i (-ζ) t ht]
    exact integral_homogeneousAverage_bilinear_transpose Q i t ht ζ f g
  · have ht₀ : t = 0 := NNReal.coe_eq_zero.mp (le_antisymm (not_lt.mp ht) t.coe_nonneg)
    subst t
    simp only [homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_apply]

end EinsteinFull
