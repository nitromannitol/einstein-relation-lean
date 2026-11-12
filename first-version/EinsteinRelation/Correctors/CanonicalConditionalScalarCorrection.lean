import EinsteinRelation.Correctors.CanonicalConditionalCenterVersions
import EinsteinRelation.Correctors.LocalMollifierUniformCorrections

/-! # Scalar correction estimate for the common conditional fields

Source: `paper/main.tex:942–963`. The source normalization is supplied as
an actual identity with a centered value and shifted mean. The existing
cancellation estimate then controls the literal derivative correction of
the same field used for the spatial equations.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors
attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

/-- The scalar conditional tail and shifted mean bound control the common
field's actual scalar correction. Source: `paper/main.tex:942–963`. The
constant is chosen before the law, source fields and moment exponent. -/
theorem canonicalConditionalMollifierFields_scalarCorrection_bound (d : ℕ) :
    ∃ W : ℝ, 0 < W ∧ ∀ {L r₀ R : ℝ}
      (Q : EnvironmentLaw d L r₀) (i : Fin d) (_hR : 1 ≤ R)
      (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
      (_hum : StronglyMeasurable (Function.uncurry u))
      (_hui : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
        Integrable (fun ω => u ω (-y.1)) (reducedEnvironmentLaw Q))
      (f : FieldPair d → ℝ) (_hf : Integrable f (reducedEnvironmentLaw Q))
      (g : {y : Vec d // euclideanNorm y ≤ R} → FieldPair d → ℝ)
      (_hgi : ∀ y, Integrable (g y) (reducedEnvironmentLaw Q))
      (_hsource : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
        (fun ω => u (translate y.1 ω) (-y.1)) =ᵐ[reducedEnvironmentLaw Q] f + g y)
      (p A B : ℝ) (_hp : 1 ≤ p) (_hA : 0 ≤ A) (_hB : 0 ≤ B)
      (_hshift : ∀ y, eLpNorm (g y) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
        ENNReal.ofReal B)
      (_htail : eLpNorm (f - (reducedEnvironmentLaw Q)[f |
        reducedCoefficientObservationSigma
          {z : Vec d | euclideanNorm (z - 0) < 8 * R}])
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A),
      MemLp (fun ω => euclideanNorm
        ((canonicalConditionalMollifierFields Q i R u S).scalarCorrection ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
      eLpNorm (fun ω => euclideanNorm
        ((canonicalConditionalMollifierFields Q i R u S).scalarCorrection ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
            ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹) := by
  obtain ⟨W, hW, hw⟩ := exists_uniform_mollifier_derivative_weights d
  refine ⟨W, hW, ?_⟩
  intro L r₀ R Q i hR u S hum hui f hf g hgi hsource p A B hp hA hB hshift htail
  letI : StandardBorelSpace (FieldPair d) := ReductionImageV3.fieldPair_standardBorel d
  letI := finiteMeasure_mollifierCenterDomain (d := d) R
  obtain ⟨hwm, hwi, hw0, hwbound⟩ := hw R (zero_lt_one.trans_le hR)
  let v : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → ℝ := fun z =>
    conditionalSpatialAverage
      (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
      (reducedEnvironmentLaw Q) u (translate z.1.1 z.2) (-z.1.1)
  have hvm : Measurable v := measurable_centered_conditionalSpatialAverage Q u hum
  have hv (y : {y : Vec d // euclideanNorm y ≤ R}) :
      (fun ω => v (y, ω)) =ᵐ[reducedEnvironmentLaw Q]
        (reducedEnvironmentLaw Q)[f + g y | reducedCoefficientObservationSigma
          {x : Vec d | euclideanNorm (x - y.1) < 32 * R}] :=
    (centered_conditionalSpatialAverage_ae_eq_condExp Q R u hum y.1 (hui y)).trans
      (condExp_congr_ae (hsource y))
  obtain ⟨hint, _, hmem, hb⟩ := local_center_conditioned_scalar_derivative_bound
    hR volume hp hA hB (fun y => gradient (Calculus.unitMassScaledMollifier d R) (-y.1))
    hwm hwi hw0 hwbound f hf g hgi hshift htail v hvm hv
  have heq : (canonicalConditionalMollifierFields Q i R u S).scalarCorrection =ᵐ[
      reducedEnvironmentLaw Q] (fun ω => ∫ y,
        v (y, ω) • gradient (Calculus.unitMassScaledMollifier d R) (-y.1)) := by
    filter_upwards [hint] with ω hi
    funext j
    change (∫ y, conditionalSpatialAverage
      (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
      (reducedEnvironmentLaw Q) u (translate y ω) (-y) *
        coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y)) = _
    rw [mollifier_derivative_integral_eq_centerIntegral (zero_lt_one.trans_le hR)]
    exact ContinuousLinearMap.integral_comp_comm (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) hi
  have hn := heq.mono fun _ h => congrArg euclideanNorm h
  exact ⟨(memLp_congr_ae hn).mpr hmem, (eLpNorm_congr_ae hn).trans_le hb⟩

end EinsteinRelation.Correctors
