import EinsteinRelation.Correctors.LocalConditionalTranslation
import EinsteinRelation.Correctors.ConditionalWeakEquation
import EinsteinRelation.Correctors.LocalCenterGeometry
import EinsteinRelation.Environment.ReductionImageSupport

/-! # Joint local conditional versions of stationary orbit fields

Source: `paper/main.tex:913–938,968–973`. A single conditional probability
kernel gives joint spatial versions at center zero. Translation then gives
joint versions over all centers, measurable using only the containing
coefficient window. The field and its orbit are the given actual observables.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- Construct a joint version of the conditional orbit, with its exact
conditional-expectation identity at every spatial point and translated
center. Source: `paper/main.tex:913–938`. -/
theorem exists_joint_local_conditional_orbit {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (U : Set (Vec d))
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfi : Integrable f (reducedEnvironmentLaw Q)) :
    ∃ v : Vec d → FieldPair d → ℝ,
      (@Measurable (Vec d × FieldPair d) ℝ
        (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _
          (reducedCoefficientObservationSigma U)) inferInstance (Function.uncurry v)) ∧
      (∀ x, v x =ᵐ[reducedEnvironmentLaw Q]
        (reducedEnvironmentLaw Q)[fun ω => f (translate x ω) |
          reducedCoefficientObservationSigma U]) ∧
      (∀ x y, (fun ω => v (x - y) (translate y ω)) =ᵐ[reducedEnvironmentLaw Q]
        (reducedEnvironmentLaw Q)[fun ω => f (translate x ω) |
          reducedCoefficientObservationSigma {z | z - y ∈ U}]) := by
  letI : StandardBorelSpace (FieldPair d) := ReductionImageV3.fieldPair_standardBorel d
  let u : FieldPair d → Vec d → ℝ := fun ω x => f (translate x ω)
  have hum : StronglyMeasurable (Function.uncurry u) :=
    (hf.comp (Probability.continuous_translate.measurable.comp measurable_swap)).stronglyMeasurable
  let v : Vec d → FieldPair d → ℝ := fun x ω =>
    conditionalSpatialAverage (reducedCoefficientObservationSigma U)
      (reducedEnvironmentLaw Q) u ω x
  have hvm : @Measurable (Vec d × FieldPair d) ℝ
      (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _
        (reducedCoefficientObservationSigma U)) inferInstance (Function.uncurry v) :=
    (stronglyMeasurable_conditionalSpatialAverage
      (reducedCoefficientObservationSigma U) (reducedEnvironmentLaw Q) u hum).measurable.comp
        measurable_swap
  have hle : reducedCoefficientObservationSigma U ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    have heval : Measurable (fun (ω : FieldPair d) (x : U) => ω.1 x) :=
      measurable_pi_lambda _ fun x =>
        ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable
    exact heval.comap_le
  have hversion (x : Vec d) : v x =ᵐ[reducedEnvironmentLaw Q]
      (reducedEnvironmentLaw Q)[fun ω => f (translate x ω) |
        reducedCoefficientObservationSigma U] := by
    have hpres : MeasurePreserving (translate x)
        (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
      ⟨Probability.measurable_translate x, reducedEnvironmentLaw_stationary Q x⟩
    exact conditionalSpatialAverage_ae_eq_condExp (reducedCoefficientObservationSigma U)
      (reducedEnvironmentLaw Q) hle u x (hpres.integrable_comp_of_integrable hfi)
  exact ⟨v, hvm, hversion, translated_local_conditional_version Q U hf hfi v hversion⟩

/-- The actual conditioned observable at centers in `B_R` has a joint
version observed in `B_{33R}`. Its sections agree with conditioning on
`B_{32R}(y)`. Source: `paper/main.tex:931–938,968–973`. -/
theorem exists_joint_center_conditioned_orbit {d : ℕ} {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfi : Integrable f (reducedEnvironmentLaw Q)) :
    ∃ u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → ℝ,
      (@Measurable ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d) ℝ
        (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}))
        inferInstance u) ∧
      ∀ y : {y : Vec d // euclideanNorm y ≤ R},
        (fun ω => u (y, ω)) =ᵐ[reducedEnvironmentLaw Q]
          (reducedEnvironmentLaw Q)[f | reducedCoefficientObservationSigma
            {z | euclideanNorm (z - y.1) < 32 * R}] := by
  obtain ⟨v, hvm, _, hversion⟩ :=
    exists_joint_local_conditional_orbit Q {z | euclideanNorm z < 32 * R} hf hfi
  refine ⟨fun p => v (0 - p.1.1) (translate p.1.1 p.2), ?_, ?_⟩
  · apply measurable_centered_local_observable (U := {z | euclideanNorm z < 32 * R})
      (S := {y | euclideanNorm y ≤ R}) (W := {z | euclideanNorm z < 33 * R})
      (F := v) _ hvm (0 : Vec d)
    intro y hy z hz
    have hnorm := TimeChange.euclideanNorm_add_le y z
    change euclideanNorm y ≤ R at hy
    change euclideanNorm z < 32 * R at hz
    change euclideanNorm (y + z) < 33 * R
    linarith
  · intro y
    simpa only [translate_zero] using hversion (0 : Vec d) y.1

/-- Coordinatewise construction gives joint versions for actual vector
orbit fields, with their literal vector-valued conditional expectation.
Source: `paper/main.tex:968–973`. -/
theorem exists_joint_center_conditioned_vector_orbit {d : ℕ} {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) {f : FieldPair d → Vec d} (hf : Measurable f)
    (hfi : Integrable f (reducedEnvironmentLaw Q)) :
    ∃ u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Vec d,
      (@Measurable ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d) (Vec d)
        (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}))
        inferInstance u) ∧
      ∀ y : {y : Vec d // euclideanNorm y ≤ R},
        (fun ω => u (y, ω)) =ᵐ[reducedEnvironmentLaw Q]
          (reducedEnvironmentLaw Q)[f | reducedCoefficientObservationSigma
            {z | euclideanNorm (z - y.1) < 32 * R}] := by
  have hscalar (j : Fin d) := exists_joint_center_conditioned_orbit (R := R) Q
    ((measurable_pi_apply j).comp hf)
    ((ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).integrable_comp hfi)
  choose u hum huv using hscalar
  have humvec : @Measurable ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d) (Vec d)
      (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}))
      inferInstance (fun p j => u j p) := by
    letI : MeasurableSpace (FieldPair d) :=
      reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}
    exact measurable_pi_lambda _ hum
  refine ⟨fun p j => u j p, humvec, ?_⟩
  intro y
  have hversion := ae_all_iff.mpr (fun j => huv j y)
  have hcoord : ∀ᵐ ω ∂reducedEnvironmentLaw Q, ∀ j : Fin d,
      (reducedEnvironmentLaw Q)[f | reducedCoefficientObservationSigma
        {z | euclideanNorm (z - y.1) < 32 * R}] ω j =
      (reducedEnvironmentLaw Q)[fun a => f a j | reducedCoefficientObservationSigma
        {z | euclideanNorm (z - y.1) < 32 * R}] ω := by
    apply ae_all_iff.mpr
    intro j
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).comp_condExp_comm
        (m := reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R}) hfi
  filter_upwards [hversion, hcoord] with ω hv hc
  funext j
  exact (hv j).trans (hc j).symm

end EinsteinRelation.Correctors
