import EinsteinRelation.Correctors.JointCenterConditionalFamily

/-! # Joint conditioning of center-dependent vector corrector fields

Source: `paper/main.tex:913–938,968–973`. Each coordinate of a vector
observable is selected by the scalar joint family. The coordinate
projections then identify the vector conditional expectation.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- Coordinatewise construction gives joint versions for center-dependent
vector observables, with their literal vector-valued conditional
expectation at every center. Source: `paper/main.tex:968–973`. -/
theorem exists_joint_center_conditioned_vector_family {d : ℕ} {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (f : Vec d × FieldPair d → Vec d)
    (hf : Measurable f)
    (hfi : ∀ y, Integrable (fun ω => f (y, ω)) (reducedEnvironmentLaw Q)) :
    ∃ u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Vec d,
      (@Measurable ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d) (Vec d)
        (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}))
        inferInstance u) ∧
      ∀ y : {y : Vec d // euclideanNorm y ≤ R},
        (fun ω => u (y, ω)) =ᵐ[reducedEnvironmentLaw Q]
          (reducedEnvironmentLaw Q)[fun ω => f (y.1, ω) | reducedCoefficientObservationSigma
            {z | euclideanNorm (z - y.1) < 32 * R}] := by
  have hscalar (j : Fin d) := exists_joint_center_conditioned_family (R := R) Q
    (fun p => f p j) ((measurable_pi_apply j).comp hf)
    (fun y => (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).integrable_comp (hfi y))
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
      (reducedEnvironmentLaw Q)[fun a => f (y.1, a) | reducedCoefficientObservationSigma
        {z | euclideanNorm (z - y.1) < 32 * R}] ω j =
      (reducedEnvironmentLaw Q)[fun a => f (y.1, a) j | reducedCoefficientObservationSigma
        {z | euclideanNorm (z - y.1) < 32 * R}] ω := by
    apply ae_all_iff.mpr
    intro j
    simpa only [Function.comp_def, ContinuousLinearMap.proj_apply] using
      (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).comp_condExp_comm
        (m := reducedCoefficientObservationSigma {z | euclideanNorm (z - y.1) < 32 * R})
        (hfi y.1)
  filter_upwards [hversion, hcoord] with ω hv hc
  funext j
  exact (hv j).trans (hc j).symm

end EinsteinRelation.Correctors
