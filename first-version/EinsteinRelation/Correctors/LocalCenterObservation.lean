import EinsteinRelation.Correctors.ReducedLocalTranslationMeasurability
import EinsteinRelation.Correctors.LocalCenterGeometry
import EinsteinRelation.Correctors.CenterAverageCovariance
import EinsteinRelation.Correctors.SubtypeIntegralMeasurability

/-! # Coefficient locality of center-averaged versions

Source: `paper/main.tex:931–938`. A center-zero version observed in the
radius-32R coefficient ball is translated to every contributing center.
Its radius-R weighted center average observes only the radius-33R ball.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)
open EinsteinRelation.TimeChange

namespace EinsteinRelation.Correctors

/-- Compact center averaging of a joint local version has exactly the
radius-33R coefficient observation required by Proposition 5.3.
Source: `paper/main.tex:931–938`. -/
theorem measurable_local_center_average {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (R : ℝ) (w : Vec d → ℝ) (hw : Measurable w)
    (hsupp : Function.support (fun y => w (0 - y)) ⊆ {y | euclideanNorm y ≤ R})
    (F : Vec d → FieldPair d → E)
    (hF : @Measurable (Vec d × FieldPair d) E
      (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 32 * R}))
      inferInstance (Function.uncurry F)) :
    @Measurable (FieldPair d) E
      (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}) inferInstance
      (fun ω => ∫ y, w (0 - y) • F (0 - y) (translate y ω) ∂volume) := by
  let S : Set (Vec d) := {y | euclideanNorm y ≤ R}
  have hS : MeasurableSet S := by
    have hc : Continuous (euclideanNorm (d := d)) := by
      unfold euclideanNorm euclideanSq dot
      fun_prop
    exact measurableSet_le hc.measurable measurable_const
  have hSW : ∀ y ∈ S, ∀ z : Vec d, euclideanNorm z < 32 * R →
      euclideanNorm (y + z) < 33 * R := by
    intro y hy z hz
    have ht := euclideanNorm_add_le y z
    change euclideanNorm y ≤ R at hy
    linarith
  have hlocal := measurable_centered_local_observable (S := S)
    (U := {z | euclideanNorm z < 32 * R})
    (W := {z | euclideanNorm z < 33 * R}) hSW F hF (0 : Vec d)
  have hweight : @Measurable (S × FieldPair d) ℝ
      (@Prod.instMeasurableSpace S (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}))
      inferInstance (fun p => w (0 - (p.1 : Vec d))) :=
    hw.comp (measurable_const.sub (measurable_subtype_coe.comp measurable_fst))
  have hm := @measurable_setIntegral_of_measurable_subtype (Vec d) (FieldPair d) E
    inferInstance (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})
    _ _ _ _ _ _ volume _ S hS
    (fun y ω => w (0 - y) • F (0 - y) (translate y ω)) (hweight.smul hlocal)
  have heq (ω : FieldPair d) :
      (∫ y in S, w (0 - y) • F (0 - y) (translate y ω) ∂volume) =
        ∫ y, w (0 - y) • F (0 - y) (translate y ω) ∂volume := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    have hwy : w (0 - y) = 0 := by
      by_contra hn
      exact hy (hsupp hn)
    rw [hwy, zero_smul]
  simpa only [heq] using hm

/-- At every spatial point, the stationary average has the required
translated radius-33R coefficient observation. Source: `paper/main.tex:931–938`. -/
theorem measurable_local_center_average_at {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (R : ℝ) (x : Vec d) (w : Vec d → ℝ) (hw : Measurable w)
    (hsupp : Function.support (fun y => w (0 - y)) ⊆ {y | euclideanNorm y ≤ R})
    (F : Vec d → FieldPair d → E)
    (hF : @Measurable (Vec d × FieldPair d) E
      (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 32 * R}))
      inferInstance (Function.uncurry F)) :
    @Measurable (FieldPair d) E
      (reducedCoefficientObservationSigma {z | euclideanNorm (z - x) < 33 * R}) inferInstance
      (fun ω => ∫ y, w (x - y) • F (x - y) (translate y ω) ∂volume) := by
  have hm := measurable_local_center_average R w hw hsupp F hF
  have ht := measurable_translate_reducedObservation (U := {z | euclideanNorm z < 33 * R})
    (W := {z | euclideanNorm (z - x) < 33 * R}) x (by
      intro y hy
      simpa only [Set.mem_setOf_eq, add_sub_cancel_left] using hy)
  have hcomp := hm.comp ht
  have heq (ω : FieldPair d) := centerAverage_translatedField_eq_orbit w F x ω
  simpa only [heq] using hcomp

end EinsteinRelation.Correctors
