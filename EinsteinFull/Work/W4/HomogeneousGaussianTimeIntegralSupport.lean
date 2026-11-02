import EinsteinFull.Work.W4.HomogeneousGaussianTimeDerivativeSupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-!+# Positive-time fundamental theorem for the actual stationary Gaussian evolution

The derivative is the literal derivative-kernel translation integral. Continuity
uses an integrable polynomial-Gaussian envelope in the spatial variable; all
time integrals take values in stationary L2, rather than an operator space.
-/

namespace EinsteinFull

open MeasureTheory Filter Set
open scoped Topology BigOperators
open EinsteinRelation

variable {d : ℕ} {Λ r : ℝ}

/-- The actual strong L2 time derivative, extended by zero off positive time. -/
noncomputable def homogeneousGaussianEvolutionTimeDerivative (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (ζ : ℂ) (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) :
    Lp ℂ 2 (reducedLaw Q) :=
  if ht : 0 < t then
    ∫ x : Vec d, homogenizedGaussianKernelTimeDerivative Q i t ht ζ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f
  else 0

/-- Pointwise time continuity of the literal derivative kernel on positive time. -/
theorem continuousAt_homogenizedGaussianKernelTimeDerivative
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
  apply (hm.fun_mul hK).congr_of_eventuallyEq
  filter_upwards [eventually_gt_nhds hs] with t ht
  simp only [dif_pos ht, homogenizedGaussianKernelTimeDerivative]

/-- L1 continuity of the derivative kernel: its literal spatial norm difference
has integral tending to zero. No operator-norm continuity is used. -/
theorem tendsto_integral_norm_homogenizedGaussianKernelTimeDerivative_sub
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ) (s : ℝ) (hs : 0 < s) :
    Tendsto (fun t => ∫ x : Vec d,
      ‖(if ht : 0 < t then homogenizedGaussianKernelTimeDerivative Q i t ht ζ x else 0) -
        homogenizedGaussianKernelTimeDerivative Q i s hs ζ x‖) (𝓝 s) (𝓝 0) := by
  obtain ⟨B, hB, _, hbound⟩ :=
    exists_integrable_homogenizedGaussianKernelTimeDerivative_bound d Λ (s / 2) (2 * s)
      (by positivity) (by positivity) ζ Q.ellipticity_parameter
  have hwin : ∀ᶠ t in 𝓝 s, 0 < t ∧ s / 2 ≤ t ∧ t ≤ 2 * s := by
    filter_upwards [eventually_gt_nhds (show s / 2 < s by linarith),
      eventually_lt_nhds (show s < 2 * s by linarith)] with t htlo hthi
    exact ⟨by linarith, htlo.le, hthi.le⟩
  have hmeas : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (fun x : Vec d =>
      ‖(if ht : 0 < t then homogenizedGaussianKernelTimeDerivative Q i t ht ζ x else 0) -
        homogenizedGaussianKernelTimeDerivative Q i s hs ζ x‖) := by
    filter_upwards [hwin] with t ht
    simpa only [dif_pos ht.1] using!
      ((integrable_homogenizedGaussianKernelTimeDerivative Q i t ht.1 ζ).sub
        (integrable_homogenizedGaussianKernelTimeDerivative Q i s hs ζ)).norm.aestronglyMeasurable
  have hdom : ∀ᶠ t in 𝓝 s, ∀ᵐ x : Vec d,
      ‖‖(if ht : 0 < t then homogenizedGaussianKernelTimeDerivative Q i t ht ζ x else 0) -
        homogenizedGaussianKernelTimeDerivative Q i s hs ζ x‖‖ ≤ B x + B x := by
    filter_upwards [hwin] with t ht
    refine Eventually.of_forall fun x => ?_
    rw [norm_norm, dif_pos ht.1]
    exact (norm_sub_le _ _).trans (add_le_add
      (hbound r Q i t ht.1 ht.2.1 ht.2.2 x)
      (hbound r Q i s hs (by linarith) (by linarith) x))
  have hlim : ∀ᵐ x : Vec d, Tendsto (fun t =>
      ‖(if ht : 0 < t then homogenizedGaussianKernelTimeDerivative Q i t ht ζ x else 0) -
        homogenizedGaussianKernelTimeDerivative Q i s hs ζ x‖) (𝓝 s) (𝓝 (0 : ℝ)) := by
    refine Eventually.of_forall fun x => ?_
    simpa only [Pi.sub_apply, dif_pos hs, sub_self, norm_zero] using!
      ((continuousAt_homogenizedGaussianKernelTimeDerivative Q i ζ x s hs).sub
        (continuousAt_const (y := homogenizedGaussianKernelTimeDerivative Q i s hs ζ x))).norm.tendsto
  simpa only [integral_zero] using!
    tendsto_integral_filter_of_dominated_convergence (fun x => B x + B x)
      hmeas hdom (hB.add hB) hlim

/-- Strong continuity of the actual L2 derivative curve at every positive time. -/
theorem continuousAt_homogeneousGaussianEvolutionTimeDerivative
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) (s : ℝ) (hs : 0 < s) :
    ContinuousAt (homogeneousGaussianEvolutionTimeDerivative Q i ζ f) s := by
  obtain ⟨B, hB, _, hbound⟩ :=
    exists_integrable_homogenizedGaussianKernelTimeDerivative_bound d Λ (s / 2) (2 * s)
      (by positivity) (by positivity) ζ Q.ellipticity_parameter
  let F : ℝ → Vec d → Lp ℂ 2 (reducedLaw Q) := fun t x =>
    (if ht : 0 < t then homogenizedGaussianKernelTimeDerivative Q i t ht ζ x else 0) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f
  have hwin : ∀ᶠ t in 𝓝 s, 0 < t ∧ s / 2 ≤ t ∧ t ≤ 2 * s := by
    filter_upwards [eventually_gt_nhds (show s / 2 < s by linarith),
      eventually_lt_nhds (show s < 2 * s by linarith)] with t htlo hthi
    exact ⟨by linarith, htlo.le, hthi.le⟩
  have hmeas : ∀ᶠ t in 𝓝 s, AEStronglyMeasurable (F t) := by
    filter_upwards [hwin] with t ht
    simpa only [F, dif_pos ht.1] using!
      (integrable_homogeneousAverageTimeDerivative_integrand Q i t ht.1 ζ f).aestronglyMeasurable
  have hdom : ∀ᶠ t in 𝓝 s, ∀ᵐ x : Vec d, ‖F t x‖ ≤ B x * ‖f‖ := by
    filter_upwards [hwin] with t ht
    refine Eventually.of_forall fun x => ?_
    simp only [F, dif_pos ht.1, norm_smul, norm_complexTranslation]
    exact mul_le_mul_of_nonneg_right
      (hbound r Q i t ht.1 ht.2.1 ht.2.2 x) (norm_nonneg f)
  have hc : ContinuousAt (fun t => ∫ x, F t x) s := by
    apply continuousAt_of_dominated hmeas hdom (hB.mul_const ‖f‖)
    exact Eventually.of_forall fun x =>
      (continuousAt_homogenizedGaussianKernelTimeDerivative Q i ζ x s hs).smul continuousAt_const
  have heq : (fun t => ∫ x, F t x) = homogeneousGaussianEvolutionTimeDerivative Q i ζ f := by
    funext t
    by_cases ht : 0 < t
    · simp only [F, homogeneousGaussianEvolutionTimeDerivative, dif_pos ht]
    · simp only [F, homogeneousGaussianEvolutionTimeDerivative, dif_neg ht,
        zero_smul, integral_zero]
  rwa [heq] at hc

/-- The actual strong derivative is continuous on every positive time window. -/
theorem continuousOn_homogeneousGaussianEvolutionTimeDerivative
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ContinuousOn (homogeneousGaussianEvolutionTimeDerivative Q i ζ f) (Ioi 0) :=
  fun s hs => (continuousAt_homogeneousGaussianEvolutionTimeDerivative Q i ζ f s hs).continuousWithinAt

/-- Bochner time integrability of the literal L2 derivative on a positive compact interval. -/
theorem intervalIntegrable_homogeneousGaussianEvolutionTimeDerivative
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (homogeneousGaussianEvolutionTimeDerivative Q i ζ f) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rw [uIcc_of_le hab]
  exact (continuousOn_homogeneousGaussianEvolutionTimeDerivative Q i ζ f).mono
    (fun _ ht => lt_of_lt_of_le ha ht.1)

/-- Positive-time fundamental theorem for arbitrary actual stationary L2 data.
The integrand is the literal derivative-kernel translation integral. -/
theorem homogeneousGaussianEvolution_sub_eq_integral_timeDerivative
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (f : Lp ℂ 2 (reducedLaw Q)) (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    homogeneousGaussianEvolution Q i ζ ⟨b, (ha.trans_le hab).le⟩ f -
      homogeneousGaussianEvolution Q i ζ ⟨a, ha.le⟩ f =
      ∫ t in a..b, homogeneousGaussianEvolutionTimeDerivative Q i ζ f t := by
  have hderiv : ∀ t ∈ uIcc a b, HasDerivAt
      (fun t : ℝ => homogeneousGaussianEvolution Q i ζ ⟨max t 0, le_max_right _ _⟩ f)
      (homogeneousGaussianEvolutionTimeDerivative Q i ζ f t) t := by
    intro t ht
    rw [uIcc_of_le hab] at ht
    have ht0 : 0 < t := ha.trans_le ht.1
    simpa only [homogeneousGaussianEvolutionTimeDerivative, dif_pos ht0] using!
      hasDerivAt_homogeneousGaussianEvolution_time Q i ζ f t ht0
  have heq := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (intervalIntegrable_homogeneousGaussianEvolutionTimeDerivative Q i ζ f a b ha hab)
  simpa only [max_eq_left ha.le, max_eq_left (ha.trans_le hab).le] using heq.symm

end EinsteinFull
