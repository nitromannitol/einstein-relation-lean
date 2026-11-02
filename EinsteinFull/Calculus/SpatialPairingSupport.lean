import EinsteinFull.Calculus.ComplexTranslationSupport
import EinsteinFull.Frozen.ScaledJointPairing
import EinsteinFull.Frozen.SchwartzTestNorm
import EinsteinFull.Frozen.ReducedLawProbability
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

open MeasureTheory

namespace EinsteinFull
open EinsteinRelation

theorem integrable_kernel_complexTranslation {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (f : Vec d → ℂ)
    (hf : Integrable f) (hc : Continuous f) (U : Lp ℂ 2 Q) :
    Integrable (fun x => f x • complexTranslation Q hQ x U) := by
  have ht : Continuous (fun x : Vec d => complexTranslation Q hQ x U) :=
    (continuous_complexTranslation Q hQ).comp (continuous_id.prodMk continuous_const)
  apply (hf.norm.mul_const ‖U‖).mono' (hc.fun_smul ht).aestronglyMeasurable
  filter_upwards [] with x
  rw [norm_smul, norm_complexTranslation]


theorem integrable_scaledJointPairing_integrand {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    Integrable (fun x : Vec d => ∑ a : JointObservationIndex d,
      F (R⁻¹ • x) a • complexTranslation (reducedLaw Q)
        (reducedLaw_stationary Q) x (Z a)) := by
  letI := reducedLaw_probability Q
  apply integrable_finset_sum
  intro a _
  have hf : Integrable (fun x : Vec d => F x a) := by
    apply F.integrable.mono ((PiLp.continuous_apply 2 _ a).comp F.continuous).aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun x => PiLp.norm_apply_le (F x) a)
  apply integrable_kernel_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q)
    (fun x => F (R⁻¹ • x) a) (hf.comp_smul (inv_ne_zero (ne_of_gt hR)))
  exact ((PiLp.continuous_apply 2 _ a).comp F.continuous).comp
    (continuous_id.const_smul R⁻¹)

end EinsteinFull
