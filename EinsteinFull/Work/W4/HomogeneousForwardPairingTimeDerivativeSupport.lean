import EinsteinFull.Work.W4.HomogeneousGaussianTimeDerivativeSupport
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Mul

/-!
Positive interior time interaction of the actual forward evolution with the
opposite-force homogeneous Gaussian evolution. Pairings are bilinear. The
forward datum belongs to the actual full generator graph; no weak-data or
coefficient-defect flux identity is asserted here.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators
noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ r : ℝ}

/-- Full positive-time differentiation follows from the actual right generator
derivative and the continuous generator orbit, through the vector-valued FTC. -/
theorem hasDerivAt_forcedComplexEvolution_of_generator
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    {f h : Lp ℂ 2 (reducedLaw Q)} (hfh : IsComplexGeneratorPair Q i ζ f h)
    (s : ℝ) (hs : 0 < s) :
    HasDerivAt (fun t : ℝ => forcedComplexEvolution Q i ζ t.toNNReal f)
      (forcedComplexEvolution Q i ζ s.toNNReal h) s := by
  have hP := isComplexEnvironmentSemigroup_forcedComplexEvolution Q i ζ
  have hu := (continuous_forcedComplexEvolution_apply Q i ζ f).comp continuous_real_toNNReal
  have hv := (continuous_forcedComplexEvolution_apply Q i ζ h).comp continuous_real_toNNReal
  have he (t : ℝ) (ht : 0 ≤ t) :
      (∫ u in (0 : ℝ)..t, forcedComplexEvolution Q i ζ u.toNNReal h) =
        forcedComplexEvolution Q i ζ t.toNNReal f - f := by
    have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hu.continuousOn
      (fun u hu => (hP.hasDerivWithinAt_orbit hfh u hu.1.le).mono Ioi_subset_Ici_self)
      (hv.intervalIntegrable 0 t)
    simpa only [Function.comp_apply, Real.toNNReal_zero, forcedComplexEvolution_zero,
      ContinuousLinearMap.id_apply] using! hi
  have hd := (intervalIntegral.integral_hasDerivAt_right (hv.intervalIntegrable 0 s)
    hv.aestronglyMeasurable.stronglyMeasurableAtFilter hv.continuousAt).add_const f
  apply hd.congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with t ht
  change forcedComplexEvolution Q i ζ t.toNNReal f =
    (∫ u in (0 : ℝ)..t, forcedComplexEvolution Q i ζ u.toNNReal h) + f
  rw [he t ht.le, sub_add_cancel]

private theorem continuousAt_timeKernelDerivative
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ) (x : Vec d)
    (s : ℝ) (hs : 0 < s) :
    ContinuousAt (fun t => if ht : 0 < t then
      homogenizedGaussianKernelTimeDerivative Q i t ht ζ x else 0) s := by
  have hK := (hasDerivAt_homogenizedGaussianKernel_time Q i ζ x s hs).continuousAt
  have hm : ContinuousAt (fun t : ℝ =>
      (((-(d : ℝ) / (2 * t) +
        (∑ j, ∑ k, x j * ((homogenizedCoefficient Q)⁻¹) j k * x k) /
          (2 * t ^ 2) : ℝ) : ℂ) -
        ζ ^ 2 * (homogenizedCoefficient Q i i : ℂ) / 2)) s := by
    fun_prop (disch := positivity)
  apply (hm.mul hK).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with t ht
  simp only [Pi.mul_apply, dif_pos ht, homogenizedGaussianKernelTimeDerivative]

/-- Strong continuity of the literal derivative-kernel integral. This proof
uses only adopted kernel producers and spatial dominated convergence. -/
theorem continuousAt_integral_homogenizedGaussianKernelTimeDerivative
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (g : Lp ℂ 2 (reducedLaw Q)) (s : ℝ) (hs : 0 < s) :
    ContinuousAt (fun t => if ht : 0 < t then
      ∫ x : Vec d, homogenizedGaussianKernelTimeDerivative Q i t ht ζ x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g
      else 0) s := by
  obtain ⟨B, hB, _, hbound⟩ :=
    exists_integrable_homogenizedGaussianKernelTimeDerivative_bound d Λ (s / 2) (2 * s)
      (by positivity) (by positivity) ζ Q.ellipticity_parameter
  let F : ℝ → Vec d → Lp ℂ 2 (reducedLaw Q) := fun t x =>
    (if ht : 0 < t then homogenizedGaussianKernelTimeDerivative Q i t ht ζ x else 0) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g
  have hwin : ∀ᶠ t in 𝓝 s, 0 < t ∧ s / 2 ≤ t ∧ t ≤ 2 * s := by
    filter_upwards [eventually_gt_nhds (show s / 2 < s by linarith),
      eventually_lt_nhds (show s < 2 * s by linarith)] with t htlo hthi
    exact ⟨by linarith, htlo.le, hthi.le⟩
  have hmeas : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (F t) := by
    filter_upwards [hwin] with t ht
    simpa only [F, dif_pos ht.1] using!
      (integrable_homogeneousAverageTimeDerivative_integrand Q i t ht.1 ζ g).aestronglyMeasurable
  have hdom : ∀ᶠ t in 𝓝 s, ∀ᵐ x : Vec d, ‖F t x‖ ≤ B x * ‖g‖ := by
    filter_upwards [hwin] with t ht
    refine Eventually.of_forall fun x => ?_
    simp only [F, dif_pos ht.1, norm_smul, norm_complexTranslation]
    exact mul_le_mul_of_nonneg_right
      (hbound r Q i t ht.1 ht.2.1 ht.2.2 x) (norm_nonneg _)
  have hc : ContinuousAt (fun t => ∫ x, F t x) s := by
    apply continuousAt_of_dominated hmeas hdom (hB.mul_const ‖g‖)
    exact Eventually.of_forall fun x =>
      (continuousAt_timeKernelDerivative Q i ζ x s hs).smul continuousAt_const
  convert! hc using 1
  funext t
  by_cases ht : 0 < t
  · simp only [F, dif_pos ht]
  · simp only [F, dif_neg ht, zero_smul, integral_zero]

private def timePairing (Q : EnvironmentLaw d Λ r) :
    Lp ℂ 2 (reducedLaw Q) →L[ℝ] Lp ℂ 2 (reducedLaw Q) →L[ℝ] ℂ :=
  ((ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2).bilinearRestrictScalars ℝ

private theorem timePairing_apply (Q : EnvironmentLaw d Λ r)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    timePairing Q f g = ∫ ω, f ω * g ω ∂reducedLaw Q :=
  ContinuousLinearMap.lpPairing_eq_integral _ _ _

/-- The actual forward/backward bilinear interaction curve, extended to real
times by nonnegative truncation of the two semigroup parameters. -/
def homogeneousForwardPairing (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (f g : Lp ℂ 2 (reducedLaw Q)) (T s : ℝ) : ℂ :=
  timePairing Q (forcedComplexEvolution Q i ζ s.toNNReal f)
    (homogeneousGaussianEvolution Q i (-ζ) (T - s).toNNReal g)

/-- The interaction is the expectation of the product, without conjugation. -/
theorem homogeneousForwardPairing_eq_integral (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (ζ : ℂ) (f g : Lp ℂ 2 (reducedLaw Q)) (T s : ℝ) :
    homogeneousForwardPairing Q i ζ f g T s =
      ∫ ω, (forcedComplexEvolution Q i ζ s.toNNReal f) ω *
        (homogeneousGaussianEvolution Q i (-ζ) (T - s).toNNReal g) ω ∂reducedLaw Q :=
  timePairing_apply Q _ _

/-- Its derivative expression: the actual forward generator orbit minus the
literal opposite-force homogeneous derivative-kernel term. -/
def homogeneousForwardPairingDerivative (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (f h g : Lp ℂ 2 (reducedLaw Q)) (T s : ℝ) : ℂ :=
  timePairing Q (forcedComplexEvolution Q i ζ s.toNNReal h)
    (homogeneousGaussianEvolution Q i (-ζ) (T - s).toNNReal g) -
  timePairing Q (forcedComplexEvolution Q i ζ s.toNNReal f)
    (if ht : 0 < T - s then
      ∫ x : Vec d, homogenizedGaussianKernelTimeDerivative Q i (T - s) ht (-ζ) x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g
      else 0)

/-- Differentiation of the actual interaction at every positive interior time. -/
theorem hasDerivAt_homogeneousForwardPairing
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    {f h : Lp ℂ 2 (reducedLaw Q)} (hfh : IsComplexGeneratorPair Q i ζ f h)
    (g : Lp ℂ 2 (reducedLaw Q)) (T s : ℝ) (hs : 0 < s) (hsT : s < T) :
    HasDerivAt (homogeneousForwardPairing Q i ζ f g T)
      (homogeneousForwardPairingDerivative Q i ζ f h g T s) s := by
  have hf := hasDerivAt_forcedComplexEvolution_of_generator Q i ζ hfh s hs
  have hg := (hasDerivAt_homogeneousGaussianEvolution_time Q i (-ζ) g
    (T - s) (sub_pos.mpr hsT)).scomp s ((hasDerivAt_id s).const_sub T)
  have hd := (timePairing Q).hasDerivAt_of_bilinear (fun _ => hf) (fun _ => hg)
  change HasDerivAt (fun t => timePairing Q
      (forcedComplexEvolution Q i ζ t.toNNReal f)
      (homogeneousGaussianEvolution Q i (-ζ) (T - t).toNNReal g))
    (timePairing Q (forcedComplexEvolution Q i ζ s.toNNReal h)
      (homogeneousGaussianEvolution Q i (-ζ) (T - s).toNNReal g) -
      timePairing Q (forcedComplexEvolution Q i ζ s.toNNReal f)
        (if ht : 0 < T - s then
          ∫ x : Vec d, homogenizedGaussianKernelTimeDerivative Q i (T - s) ht (-ζ) x •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g
          else 0)) s
  rw [dif_pos (sub_pos.mpr hsT)]
  simpa only [Function.comp_apply, zero_sub, neg_smul, one_smul, map_neg,
    sub_eq_add_neg, add_comm] using! hd

/-- The actual interaction derivative is continuous on the open interior
window, without any caller-supplied curve equation or continuity premise. -/
theorem continuousOn_homogeneousForwardPairingDerivative
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (f h g : Lp ℂ 2 (reducedLaw Q)) (T : ℝ) :
    ContinuousOn (homogeneousForwardPairingDerivative Q i ζ f h g T) (Ioo 0 T) := by
  intro s hs
  have hf := ((continuous_forcedComplexEvolution_apply Q i ζ f).comp
    continuous_real_toNNReal).continuousAt (x := s)
  have hh := ((continuous_forcedComplexEvolution_apply Q i ζ h).comp
    continuous_real_toNNReal).continuousAt (x := s)
  have hg := ((hasDerivAt_homogeneousGaussianEvolution_time Q i (-ζ) g
    (T - s) (sub_pos.mpr hs.2)).continuousAt).comp
      (continuousAt_const.sub continuousAt_id)
  have hg' := (continuousAt_integral_homogenizedGaussianKernelTimeDerivative Q i (-ζ) g
    (T - s) (sub_pos.mpr hs.2)).comp (continuousAt_const.sub continuousAt_id)
  have hfirst := ((timePairing Q).continuous.continuousAt.comp hh).clm_apply hg
  have hsecond := ((timePairing Q).continuous.continuousAt.comp hf).clm_apply hg'
  simpa only [homogeneousForwardPairingDerivative, Function.comp_apply] using!
    (hfirst.sub hsecond).continuousWithinAt

/-- Integrability of the actual derivative expression on each positive compact
interior time window, including a degenerate window. -/
theorem intervalIntegrable_homogeneousForwardPairingDerivative
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (f h g : Lp ℂ 2 (reducedLaw Q)) (T a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    IntervalIntegrable (homogeneousForwardPairingDerivative Q i ζ f h g T) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact (continuousOn_homogeneousForwardPairingDerivative Q i ζ f h g T).mono
    (fun _ ht => ⟨ha.trans_le ht.1, ht.2.trans_lt hbT⟩)

/-- The time interaction identity derived from the actual generator-domain
forward curve and arbitrary L2 backward Gaussian datum. Extension to arbitrary
forward L2 or centered weak data requires a later energy approximation. -/
theorem homogeneousForwardPairing_sub_eq_integral
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    {f h : Lp ℂ 2 (reducedLaw Q)} (hfh : IsComplexGeneratorPair Q i ζ f h)
    (g : Lp ℂ 2 (reducedLaw Q)) (T a b : ℝ)
    (ha : 0 < a) (hab : a ≤ b) (hbT : b < T) :
    homogeneousForwardPairing Q i ζ f g T b -
      homogeneousForwardPairing Q i ζ f g T a =
      ∫ s in a..b, homogeneousForwardPairingDerivative Q i ζ f h g T s := by
  apply Eq.symm
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := homogeneousForwardPairing Q i ζ f g T)
  · intro s hs
    rw [uIcc_of_le hab] at hs
    exact hasDerivAt_homogeneousForwardPairing Q i ζ hfh g T s
      (ha.trans_le hs.1) (hs.2.trans_lt hbT)
  · exact intervalIntegrable_homogeneousForwardPairingDerivative Q i ζ f h g T a b ha hab hbT

end EinsteinFull
