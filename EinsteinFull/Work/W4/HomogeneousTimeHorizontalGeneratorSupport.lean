import EinsteinFull.Work.W4.HomogeneousHorizontalCalculusSupport
import EinsteinFull.Work.W4.HomogeneousGaussianTimeIntegralSupport
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts

/-!
Spatial integration by parts for the literal Gaussian stationary integral.
The translation orbit has its genuine strong horizontal derivative; decay is
supplied by the actual anisotropic kernel, without a weak-equation premise.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ r : ℝ}
attribute [local instance] reducedLaw_probability

/-- Every positive-time kernel is Schwartz, by exact parabolic scaling of the
proved unit-time kernel. This assertion retains its literal coordinate carrier. -/
theorem exists_schwartz_homogenizedGaussianKernel (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    ∃ K : SchwartzMap (Vec d) ℂ, ∀ x, K x = homogenizedGaussianKernel Q i s hs ζ x := by
  let c := Real.sqrt s
  have hc : 0 < c := Real.sqrt_pos.mpr hs
  have hcs : c ^ 2 = s := Real.sq_sqrt hs.le
  let L := (LinearEquiv.smulOfNeZero (M := Vec d) ℝ c⁻¹ (inv_ne_zero hc.ne')).toContinuousLinearEquiv
  let K := homogenizedGaussianSchwartz Q i 1 (by norm_num) (by norm_num) le_rfl
    (ζ * (c : ℂ))
  refine ⟨(((c ^ d)⁻¹ : ℝ) : ℂ) •
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L K, fun x => ?_⟩
  change (((c ^ d)⁻¹ : ℝ) : ℂ) * K (c⁻¹ • x) = _
  have he := homogenizedGaussianKernel_scale Q i c 1 hc (by norm_num) ζ (c⁻¹ • x)
  simpa only [mul_one, hcs, smul_smul, mul_inv_cancel₀ hc.ne', one_smul,
    K, homogenizedGaussianSchwartz_apply] using he.symm

/-- Coordinate integration by parts against the actual stationary translation
orbit. A Schwartz spatial kernel supplies all three integrability requirements. -/
theorem integral_schwartz_complexTranslation_horizontalDerivative
    (Q : EnvironmentLaw d Λ r) (j : Fin d)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g)
    (K : SchwartzMap (Vec d) ℂ) :
    (∫ x : Vec d, K x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) =
      -(∫ x : Vec d, fderiv ℝ K x (unitVector j) •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) := by
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) K
  have hD (x : Vec d) : D x = fderiv ℝ K x (unitVector j) := rfl
  have hg (x : Vec d) : HasLineDerivAt ℝ
      (fun y => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y f)
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) x (unitVector j) := by
    have hd := (((complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt 0
      (hf.hasDerivAt_orbit 0)
    simp only [zero_smul, complexTranslation_zero] at hd
    change HasDerivAt (fun t : ℝ => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) (t • unitVector j) f))
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) 0 at hd
    simpa only [HasLineDerivAt, ← complexTranslation_add] using! hd

  exact integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (B := ContinuousLinearMap.lsmul ℝ ℂ)
    (by simpa only [hD] using! (integrable_kernel_complexTranslation _ _ D
      D.integrable D.continuous f))
    (integrable_kernel_complexTranslation _ _ K K.integrable K.continuous g)
    (integrable_kernel_complexTranslation _ _ K K.integrable K.continuous f)
    (fun x _ => (K.hasFDerivAt x).hasLineDerivAt (unitVector j)) (fun x _ => hg x)

private def schwartzTranslationIntegral (Q : EnvironmentLaw d Λ r)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    SchwartzMap (Vec d) ℂ →ₗ[ℂ] Lp ℂ 2 (reducedLaw Q) where
  toFun K := ∫ x : Vec d, K x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f
  map_add' K L := by
    simp only [SchwartzMap.add_apply, add_smul]
    exact integral_add
      (integrable_kernel_complexTranslation _ _ K K.integrable K.continuous f)
      (integrable_kernel_complexTranslation _ _ L L.integrable L.continuous f)
  map_smul' a K := by
    simp only [SchwartzMap.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul,
      integral_smul]

private def gaussianSpatialDerivative (K : SchwartzMap (Vec d) ℂ) (j : Fin d) :
    SchwartzMap (Vec d) ℂ :=
  (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) K

private theorem gaussianSpatialDerivative_apply (K : SchwartzMap (Vec d) ℂ)
    (j : Fin d) (x : Vec d) :
    gaussianSpatialDerivative K j x = fderiv ℝ K x (unitVector j) := rfl

/-- The literal Gaussian first derivative moves onto any genuine horizontal
first derivative, with the spatial integration-by-parts minus sign. -/
theorem integral_gaussian_complexTranslation_horizontalDerivative
    (Q : EnvironmentLaw d Λ r) (i j : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g) :
    (∫ x : Vec d, fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) x (unitVector j) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) =
      -homogeneousAverage Q i s hs ζ g := by
  obtain ⟨K, hK⟩ := exists_schwartz_homogenizedGaussianKernel Q i s hs ζ
  have he : (K : Vec d → ℂ) = homogenizedGaussianKernel Q i s hs ζ := funext hK
  have h := integral_schwartz_complexTranslation_horizontalDerivative Q j f g hf K
  rw [he] at h
  simpa only [neg_neg] using! congrArg Neg.neg h.symm

/-- Two literal spatial Gaussian derivatives move onto the actual second
horizontal derivative. Integrability and boundary removal follow from Schwartz
kernels, rather than from a supplied generator equation. -/
theorem integral_gaussian_complexTranslation_horizontalSecondDerivative
    (Q : EnvironmentLaw d Λ r) (i j k : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (f g h : Lp ℂ 2 (reducedLaw Q))
    (hf : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) k f g)
    (hg : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j g h) :
    (∫ x : Vec d, fderiv ℝ
      (fun y => fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) y (unitVector j))
      x (unitVector k) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) =
      homogeneousAverage Q i s hs ζ h := by
  obtain ⟨K, hK⟩ := exists_schwartz_homogenizedGaussianKernel Q i s hs ζ
  let D := (SchwartzMap.evalCLM ℂ (Vec d) ℂ (unitVector j)).comp (SchwartzMap.fderivCLM ℂ (Vec d) ℂ) K
  have he : (K : Vec d → ℂ) = homogenizedGaussianKernel Q i s hs ζ := funext hK
  have hD : (D : Vec d → ℂ) = fun y =>
      fderiv ℝ (homogenizedGaussianKernel Q i s hs ζ) y (unitVector j) := by
    change (fun y => fderiv ℝ K y (unitVector j)) = _
    rw [he]
  have h1 := integral_schwartz_complexTranslation_horizontalDerivative Q k f g hf D
  rw [hD] at h1
  have h2 := congrArg Neg.neg h1
  simp only [neg_neg] at h2
  rw [← h2, integral_gaussian_complexTranslation_horizontalDerivative Q i j s hs ζ g h hg,
    neg_neg]

/-- Identification of the literal Gaussian time-derivative integral on an
actual smooth horizontal jet. The two integrations by parts are spatial and
retain the positive horizontal drift of the signed complex force. -/
theorem homogeneousGaussianTimeDerivative_eq_horizontalAction
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (J : List (Fin d) → Lp ℂ 2 (reducedLaw Q)) (hJ : HasComplexHorizontalJet Q J) :
    homogeneousGaussianEvolutionTimeDerivative Q i ζ (J []) s =
      homogeneousAverage Q i s hs ζ
        (homogeneousHorizontalAction Q i ζ (fun j => J [j]) (fun j k => J [j, k])) := by
  obtain ⟨K, hK⟩ := exists_schwartz_homogenizedGaussianKernel Q i s hs ζ
  have he : (K : Vec d → ℂ) = homogenizedGaussianKernel Q i s hs ζ := funext hK
  let D := gaussianSpatialDerivative (d := d)
  let S : SchwartzMap (Vec d) ℂ :=
    (1 / 2 : ℂ) • ∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) • D (D K j) k -
      ζ • ∑ j, (homogenizedCoefficient Q j i : ℂ) • D K j
  have hS (x : Vec d) : S x = homogenizedGaussianKernelTimeDerivative Q i s hs ζ x := by
    dsimp only [S]
    simp only [sub_apply, smul_apply, sum_apply,
      smul_eq_mul, D, gaussianSpatialDerivative_apply]
    have hD (j : Fin d) : (gaussianSpatialDerivative K j : Vec d → ℂ) =
        fun y => fderiv ℝ K y (unitVector j) := rfl
    simp only [hD, he]
    convert (homogenizedGaussianKernelTimeDerivative_eq_spatial Q i s hs ζ x).symm using 1
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, mul_ite]
  have hd (j : Fin d) : schwartzTranslationIntegral Q (J []) (D K j) =
      -homogeneousAverage Q i s hs ζ (J [j]) := by
    change (∫ x : Vec d, fderiv ℝ K x (unitVector j) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (J [])) = _
    rw [he]
    exact integral_gaussian_complexTranslation_horizontalDerivative Q i j s hs ζ _ _ (hJ [] j)
  have hdd (j k : Fin d) : schwartzTranslationIntegral Q (J []) (D (D K j) k) =
      homogeneousAverage Q i s hs ζ (J [j, k]) := by
    change (∫ x : Vec d, fderiv ℝ (fun y => fderiv ℝ K y (unitVector j)) x
      (unitVector k) • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (J [])) = _
    rw [he]
    exact integral_gaussian_complexTranslation_horizontalSecondDerivative Q i j k s hs ζ
      _ _ _ (hJ [] k) (hJ [k] j)
  have hL : homogeneousGaussianEvolutionTimeDerivative Q i ζ (J []) s =
      schwartzTranslationIntegral Q (J []) S := by
    simp only [homogeneousGaussianEvolutionTimeDerivative, dif_pos hs, schwartzTranslationIntegral]
    apply integral_congr_ae
    exact Eventually.of_forall fun x => by dsimp only; rw [hS]
  rw [hL]
  dsimp only [S]
  simp only [map_sub, map_smul, map_sum, hd, hdd, smul_neg, Finset.sum_neg_distrib,
    sub_neg_eq_add]
  rw [homogeneousAverage_horizontalAction]
  rfl

/-- The actual positive-time L2 derivative equals the literal anisotropic
horizontal action of the evolved smooth jet. -/
theorem hasDerivAt_homogeneousGaussianEvolution_horizontalJet
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (J : List (Fin d) → Lp ℂ 2 (reducedLaw Q)) (hJ : HasComplexHorizontalJet Q J)
    (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => homogeneousGaussianEvolution Q i ζ
      ⟨max t 0, le_max_right _ _⟩ (J []))
      (homogeneousHorizontalAction Q i ζ
        (fun j => homogeneousAverage Q i s hs ζ (J [j]))
        (fun j k => homogeneousAverage Q i s hs ζ (J [j, k]))) s := by
  have hd := hasDerivAt_homogeneousGaussianEvolution_time Q i ζ (J []) s hs
  have he : (∫ x : Vec d, homogenizedGaussianKernelTimeDerivative Q i s hs ζ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x (J [])) =
      homogeneousGaussianEvolutionTimeDerivative Q i ζ (J []) s := by
    simp only [homogeneousGaussianEvolutionTimeDerivative, dif_pos hs]
  rw [he] at hd
  rw [homogeneousGaussianTimeDerivative_eq_horizontalAction Q i s hs ζ J hJ,
    homogeneousAverage_horizontalAction] at hd
  exact hd

/-- Full-H1 bilinear weak testing of the genuine L2 time derivative for smooth
horizontal data. The expectation is E(v*u), with no conjugation. -/
theorem homogeneousGaussianEvolutionTimeDerivative_horizontalJet_weak
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (J : List (Fin d) → Lp ℂ 2 (reducedLaw Q)) (hJ : HasComplexHorizontalJet Q J)
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, v ω * homogeneousGaussianEvolutionTimeDerivative Q i ζ (J []) s ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * ∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
        (∫ ω, V j ω * homogeneousAverage Q i s hs ζ (J [k]) ω ∂reducedLaw Q) +
      ζ * ∑ j, (homogenizedCoefficient Q j i : ℂ) *
        (∫ ω, v ω * homogeneousAverage Q i s hs ζ (J [j]) ω ∂reducedLaw Q) := by
  rw [homogeneousGaussianTimeDerivative_eq_horizontalAction Q i s hs ζ J hJ]
  exact homogeneousAverage_horizontalJet_weak Q i s hs ζ J hJ v V hv

/-- The backward homogeneous test uses the negative complex force, retaining
the same bilinear expectation and the full H1 test domain. -/
theorem homogeneousGaussianEvolutionTimeDerivative_negativeForce_horizontalJet_weak
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (J : List (Fin d) → Lp ℂ 2 (reducedLaw Q)) (hJ : HasComplexHorizontalJet Q J)
    (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hv : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
    (∫ ω, v ω * homogeneousGaussianEvolutionTimeDerivative Q i (-ζ) (J []) s ω ∂reducedLaw Q) =
      -(1 / 2 : ℂ) * ∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
        (∫ ω, V j ω * homogeneousAverage Q i s hs (-ζ) (J [k]) ω ∂reducedLaw Q) -
      ζ * ∑ j, (homogenizedCoefficient Q j i : ℂ) *
        (∫ ω, v ω * homogeneousAverage Q i s hs (-ζ) (J [j]) ω ∂reducedLaw Q) := by
  simpa only [neg_mul, sub_eq_add_neg] using!
    homogeneousGaussianEvolutionTimeDerivative_horizontalJet_weak Q i s hs (-ζ) J hJ v V hv

end EinsteinFull
