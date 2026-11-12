import EinsteinRelation.Correctors.LocalConditioningBounds

/-! # Coefficient observation of the local flux error

Source: `paper/main.tex:931–938`. The error `aH-K` uses the
coefficient only at the evaluation point, in addition to the observation
window of the two averaged fields.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- Source: `paper/main.tex:931–938`. Point evaluation is measurable
for the coefficient observation of any region containing that point. -/
theorem measurable_reduced_coefficient_evaluation {d : ℕ} {U : Set (Vec d)}
    {x : Vec d} (hx : x ∈ U) :
    @Measurable (FieldPair d) (Mat d) (reducedCoefficientObservationSigma U)
      inferInstance (fun ω => ω.1 x) := by
  apply Measurable.of_comap_le
  exact le_iSup_of_le (⟨x, hx⟩ : U) le_rfl

/-- Source: `paper/main.tex:931–938`. The actual flux error preserves
the coefficient-only observation window. -/
theorem measurable_local_flux_error {d : ℕ} {U : Set (Vec d)}
    {x : Vec d} (hx : x ∈ U) {H K : FieldPair d → Vec d}
    (hH : @Measurable (FieldPair d) (Vec d)
      (reducedCoefficientObservationSigma U) inferInstance H)
    (hK : @Measurable (FieldPair d) (Vec d)
      (reducedCoefficientObservationSigma U) inferInstance K) :
    @Measurable (FieldPair d) (Vec d) (reducedCoefficientObservationSigma U)
      inferInstance (fun ω => (ω.1 x).mulVec (H ω) - K ω) := by
  letI : MeasurableSpace (FieldPair d) := reducedCoefficientObservationSigma U
  have hA := measurable_reduced_coefficient_evaluation hx
  apply measurable_pi_lambda
  intro j
  apply Measurable.sub _ ((measurable_pi_apply j).comp hK)
  change @Measurable (FieldPair d) ℝ (reducedCoefficientObservationSigma U)
    inferInstance (fun ω => ∑ k, ω.1 x j k * H ω k)
  apply Finset.measurable_fun_sum
  intro k _
  have hc : Continuous (fun A : Mat d => A j k) :=
    (continuous_apply k).comp (continuous_apply j)
  exact (hc.measurable.comp hA).mul ((measurable_pi_apply k).comp hH)

end EinsteinRelation.Correctors
