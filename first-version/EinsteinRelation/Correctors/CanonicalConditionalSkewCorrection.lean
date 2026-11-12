import EinsteinRelation.Correctors.CanonicalConditionalCenterVersions
import EinsteinRelation.Correctors.LocalMollifierUniformCorrections
import EinsteinRelation.Correctors.ConditionalSkewColumnTail

/-! # Skew correction estimate for the common conditional fields

Source: `paper/main.tex:942–963`. The exact entrywise conditional skew
field used in the spatial equations also satisfies the columnwise cancellation
estimate. Its tail hypothesis retains the source Frobenius norm.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors
attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

/-- The source Frobenius conditional tail controls the common field's literal
skew correction. Source: `paper/main.tex:942–963`. -/
theorem canonicalConditionalMollifierFields_skewCorrection_bound (d : ℕ) :
    ∃ W : ℝ, 0 < W ∧ ∀ {L r₀ R : ℝ}
      (Q : EnvironmentLaw d L r₀) (i : Fin d) (_hR : 1 ≤ R)
      (u : FieldPair d → Vec d → ℝ) (S : FieldPair d → Vec d → Mat d)
      (_hSm : ∀ j k, StronglyMeasurable (fun z : FieldPair d × Vec d => S z.1 z.2 j k))
      (_hSi : ∀ k (y : {y : Vec d // euclideanNorm y ≤ R}),
        Integrable (fun ω j => S ω (-y.1) j k) (reducedEnvironmentLaw Q))
      (f : FieldPair d → Mat d)
      (_hf : ∀ k, Integrable (fun ω j => f ω j k) (reducedEnvironmentLaw Q))
      (g : Fin d → {y : Vec d // euclideanNorm y ≤ R} → FieldPair d → Vec d)
      (_hgi : ∀ k y, Integrable (g k y) (reducedEnvironmentLaw Q))
      (_hsource : ∀ k (y : {y : Vec d // euclideanNorm y ≤ R}),
        (fun ω j => S (translate y.1 ω) (-y.1) j k) =ᵐ[reducedEnvironmentLaw Q]
          (fun ω j => f ω j k) + g k y)
      (p A B : ℝ) (_hp : 1 ≤ p) (_hA : 0 ≤ A) (_hB : 0 ≤ B)
      (_hshift : ∀ k y, eLpNorm (fun ω => euclideanNorm (g k y ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal B)
      (_htail : eLpNorm (fun ω => frobeniusNorm (fun j k => f ω j k -
        (reducedEnvironmentLaw Q)[fun a => f a j k |
          reducedCoefficientObservationSigma
            {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A),
      MemLp (fun ω => euclideanNorm
        ((canonicalConditionalMollifierFields Q i R u S).skewCorrection ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
      eLpNorm (fun ω => euclideanNorm
        ((canonicalConditionalMollifierFields Q i R u S).skewCorrection ω))
          (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
            ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹) := by
  obtain ⟨W, hW, hw⟩ := exists_uniform_mollifier_derivative_weights d
  refine ⟨W, hW, ?_⟩
  intro L r₀ R Q i hR u S hSm hSi f hf g hgi hsource p A B hp hA hB hshift htail
  letI : StandardBorelSpace (FieldPair d) := ReductionImageV3.fieldPair_standardBorel d
  letI := finiteMeasure_mollifierCenterDomain (d := d) R
  obtain ⟨hwm, hwi, hw0, hwbound⟩ := hw R (zero_lt_one.trans_le hR)
  let v : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Mat d := fun z j k =>
    conditionalSpatialAverage
      (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
      (reducedEnvironmentLaw Q) (fun a x => S a x j k) (translate z.1.1 z.2) (-z.1.1)
  have hvm : Measurable v := by
    have hpi : @Measurable _ (Fin d → Fin d → ℝ) _ MeasurableSpace.pi v :=
      measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun k =>
        measurable_centered_conditionalSpatialAverage (R := R) Q
          (fun a x => S a x j k) (hSm j k)
    exact hpi.mono le_rfl (OpensMeasurableSpace.borel_le (α := Fin d → Fin d → ℝ))
  have hv (k : Fin d) (y : {y : Vec d // euclideanNorm y ≤ R}) :
      (fun ω j => v (y, ω) j k) =ᵐ[reducedEnvironmentLaw Q]
        (reducedEnvironmentLaw Q)[(fun ω j => f ω j k) + g k y |
          reducedCoefficientObservationSigma
            {x : Vec d | euclideanNorm (x - y.1) < 32 * R}] := by
    have hpres : MeasurePreserving (translate y.1)
        (reducedEnvironmentLaw Q) (reducedEnvironmentLaw Q) :=
      ⟨Probability.measurable_translate _, reducedEnvironmentLaw_stationary Q _⟩
    have hcol := condExp_column_ae_eq_entrywise (reducedEnvironmentLaw Q)
      (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm (x - y.1) < 32 * R})
      (fun ω => S (translate y.1 ω) (-y.1)) k
      (hpres.integrable_comp_of_integrable (hSi k y))
    have hc (j : Fin d) := centered_conditionalSpatialAverage_ae_eq_condExp Q R
      (fun a x => S a x j k) (hSm j k) y.1
      ((ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).integrable_comp (hSi k y))
    have heq : (fun ω j => v (y, ω) j k) =ᵐ[reducedEnvironmentLaw Q]
        (reducedEnvironmentLaw Q)[fun ω j => S (translate y.1 ω) (-y.1) j k |
          reducedCoefficientObservationSigma
            {x : Vec d | euclideanNorm (x - y.1) < 32 * R}] := by
      filter_upwards [ae_all_iff.mpr hc, hcol] with ω hω hcolω
      exact (funext hω).trans hcolω.symm
    exact heq.trans (condExp_congr_ae (hsource k y))
  have hcoltail (k : Fin d) : eLpNorm (fun ω => euclideanNorm
      ((fun j => f ω j k) - (reducedEnvironmentLaw Q)[fun a j => f a j k |
        reducedCoefficientObservationSigma
          {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A :=
    (eLpNorm_conditional_column_sub_le_frobenius (reducedEnvironmentLaw Q)
      (reducedCoefficientObservationSigma {z : Vec d | euclideanNorm (z - 0) < 8 * R})
      f k (hf k) (ENNReal.ofReal p)).trans htail
  obtain ⟨hint, _, hmem, hb⟩ := local_center_conditioned_skew_derivative_bound
    hR volume hp hA hB (fun y => gradient (Calculus.unitMassScaledMollifier d R) (-y.1))
    hwm hwi hw0 hwbound (fun k ω j => f ω j k) hf g hgi hshift hcoltail v hvm hv
  have hcenter : MeasurableSet {y : Vec d | euclideanNorm y ≤ R} :=
    (isClosed_le Entropy.continuous_euclideanNorm' continuous_const).measurableSet
  have heq : (canonicalConditionalMollifierFields Q i R u S).skewCorrection =ᵐ[
      reducedEnvironmentLaw Q] (fun ω => ∫ y,
        (v (y, ω)).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (-y.1))) := by
    filter_upwards [hint] with ω hi
    funext j
    let V : Vec d → Mat d := fun y a b => conditionalSpatialAverage
      (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
      (reducedEnvironmentLaw Q) (fun a' x => S a' x a b) (translate y ω) (-y)
    change (∫ y, ((V y).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (-y))) j) = _
    calc
      _ = ∫ y in {y : Vec d | euclideanNorm y ≤ R},
          ((V y).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (-y))) j := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro y hy
        have hzero : gradient (Calculus.unitMassScaledMollifier d R) (-y) = 0 := by
          funext k
          apply Entropy.coordinateDerivative_unitMassScaledMollifier_eq_zero
            (zero_lt_one.trans_le hR) k
          have hy' : R < euclideanNorm y := not_le.mp hy
          simpa only [TimeChange.euclideanNorm_eq_norm_toLp, WithLp.toLp_neg, norm_neg]
            using hy'
        rw [hzero, Matrix.mulVec_zero]
        rfl
      _ = ∫ y : {y : Vec d // euclideanNorm y ≤ R},
          ((V y.1).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (-y.1))) j :=
        (integral_subtype hcenter _).symm
      _ = _ := ContinuousLinearMap.integral_comp_comm
        (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ) hi
  have hn := heq.mono fun _ h => congrArg euclideanNorm h
  exact ⟨(memLp_congr_ae hn).mpr hmem, (eLpNorm_congr_ae hn).trans_le hb⟩

end EinsteinRelation.Correctors
