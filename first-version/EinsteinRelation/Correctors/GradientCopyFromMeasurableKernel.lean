import EinsteinRelation.Correctors.CanonicalPointCopyDecay
import EinsteinRelation.Correctors.AKMMeasurableKernelColumnFlow

/-! # Production gradient-copy estimate from coefficient-measurable kernels

Source: `paper/main.tex:852–867,878–886`. A scalar kernel jointly measurable
with its coefficient constructs the actual flow. The stationary gradient,
spatial energy, point values and physical radius scaling then give the
production conditional-copy estimate.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport ReductionImageV3
open NormalizedSpatialRepresentativeSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance kernelPointRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- The unchanged production point-copy estimate follows from measurable
scalar kernels and the existing frozen inputs. The kernel is measurable
jointly with its coefficient. Constants precede Q.
Source: `paper/main.tex:852–867,878–886`. -/
theorem gradient_copy_decay_of_measurable_kernel
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (hAKM : EllipticLargeScale) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) (H51 : CorrectorGradientMoments)
    (d : ℕ) [Fact (2 ≤ d)] (L r₀ m : ℝ) (hm : 2 ≤ m)
    (hkernel : ∀ Q : EnvironmentLaw d L r₀,
      ∃ (CK : ℝ → ℝ)
        (P : Coefficient d (AKMUpperEllipticity L) → ℝ → Vec d → Vec d → ℝ),
        (∀ α, 0 < α → α < (AKMUpperEllipticity L)⁻¹ → 0 < CK α) ∧
        Measurable (fun z :
          (Coefficient d (AKMUpperEllipticity L) × (ℝ × Vec d)) × Vec d =>
          P z.1.1 z.1.2.1 z.1.2.2 z.2) ∧
        ∀ᵐ A ∂actualCoefficientLaw Q,
          ∃ (X Y : ℝ → Vec d → Vec d → Vec d)
            (H : ℝ → Vec d → Vec d → Mat d), HeatKernelProperties A (P A) X Y H CK) :
    ∃ C : ℝ, ∀ (Q : EnvironmentLaw d L r₀) (R : ℝ), 1 ≤ R →
      ∀ (y : Point d) (i : Fin d),
      eLpNorm (fun z : C(conditionalCorrectorBall R y, Mat d) ×
        (FieldPair d × FieldPair d) =>
        euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
          conditionalCorrectorGradient Q i y z.2.2)) (ENNReal.ofReal m)
        (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) (conditionalCorrectorBall R y)) ≤
          ENNReal.ofReal (C*R^(-(d : ℝ)/2)) := by
  by_cases hL : 1 ≤ L
  swap
  · exact ⟨0,fun Q => False.elim (hL Q.ellipticity_parameter)⟩
  by_cases hr : 1 ≤ r₀
  swap
  · exact ⟨0,fun Q => False.elim (hr Q.range_parameter)⟩
  have hr0 : 0 < r₀ := zero_lt_one.trans_le hr
  obtain ⟨C,hC,hpoint⟩ := actual_canonical_point_copy_decay hdecay hreg hAKM hP
    h817 h832 h836 H51 d L r₀ m hL hr hm
  obtain ⟨D,_,hD⟩ := gradientCopy_decay_of_large_radii H51 d Fact.out L r₀ m r₀ hm hr (by
    refine ⟨C*r₀^((d : ℝ)/2),?_⟩
    intro Q R hR y i
    obtain ⟨CK,P,hCK,hPm,hPkernel⟩ := hkernel Q
    obtain ⟨u,G,hu,hG,hflow⟩ := actualCoefficientLaw_canonical_column_of_measurable_kernel
      Q i CK hCK P hPm hPkernel
    have hb := hpoint Q i u G hu hG
      (hflow.mono fun _ h => ⟨h.1,h.2.1⟩) (hflow.mono fun _ h => h.2.2.1)
      (R/r₀) ((one_le_div hr0).mpr hR) y
    have hid := continuous_gradient_copy_norm_eq hP h836 Q i R y (ENNReal.ofReal m)
    rw [show r₀*(R/r₀) = R by field_simp] at hb
    rw [hid]
    refine hb.trans (ENNReal.ofReal_le_ofReal ?_)
    have hR0 : 0 ≤ R := hr0.le.trans hR
    have heq : (R/r₀)^(-(d : ℝ)/2) = r₀^((d : ℝ)/2)*R^(-(d : ℝ)/2) := by
      rw [Real.div_rpow hR0 hr0.le,div_eq_mul_inv,← Real.rpow_neg hr0.le]
      rw [show -(-(d : ℝ)/2) = (d : ℝ)/2 by ring,mul_comm]
    rw [heq]
    ring_nf
    exact le_rfl)
  exact ⟨D,fun Q R hR y i => (hD Q R hR y i).2⟩

end EinsteinRelation.Correctors
