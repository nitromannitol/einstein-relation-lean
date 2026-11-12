import EinsteinRelation.Correctors.JointLocalConditionalOrbit
import EinsteinRelation.Correctors.LocalConditionedGradient
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport

/-! # Constructing the averaged conditional gradient

Source: `paper/main.tex:931–938,968–973`. The jointly measurable local
conditional versions are constructed from the actual orbit field. Their
normalized center average is observed in `B_{33R}` and satisfies the
Euclidean conditional-gradient error bound from `B_{8R}`.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- Construct the conditional-gradient average with exact coefficient
locality and the Euclidean error bound. The derivative-of-weight correction
is a separate part of the local corrector. Source: `paper/main.tex:968–973`. -/
theorem exists_local_conditional_gradient_average {d : ℕ} {L r₀ R p A : ℝ}
    (Q : EnvironmentLaw d L r₀) (hR : 1 ≤ R)
    (ν : Measure {y : Vec d // euclideanNorm y ≤ R}) [SigmaFinite ν]
    (hp : 1 ≤ p) (hA : 0 ≤ A)
    (w : {y : Vec d // euclideanNorm y ≤ R} → ℝ)
    (hwm : Measurable w) (hwi : Integrable w ν) (hw0 : ∀ y, 0 ≤ w y)
    (hw : (∫ y, w y ∂ν) = 1)
    (f : FieldPair d → Vec d) (hf : Integrable f (reducedEnvironmentLaw Q))
    (hfm : Measurable f)
    (htail : eLpNorm (fun ω => euclideanNorm
      (f ω - (reducedEnvironmentLaw Q)[f | reducedCoefficientObservationSigma
        {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A) :
    ∃ u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Vec d,
      Measurable u ∧
      (∀ y : {y : Vec d // euclideanNorm y ≤ R},
        (fun ω => u (y, ω)) =ᵐ[reducedEnvironmentLaw Q]
          (reducedEnvironmentLaw Q)[f | reducedCoefficientObservationSigma
            {z | euclideanNorm (z - y.1) < 32 * R}]) ∧
      (@Measurable (FieldPair d) (Vec d)
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})
        inferInstance (fun ω => ∫ y, w y • u (y, ω) ∂ν)) ∧
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun y => w y • u (y, ω)) ν) ∧
      MemLp (fun ω => euclideanNorm ((∫ y, w y • u (y, ω) ∂ν) - f ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
      eLpNorm (fun ω => euclideanNorm ((∫ y, w y • u (y, ω) ∂ν) - f ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (2 * A) := by
  obtain ⟨u, hu, hversion⟩ := exists_joint_center_conditioned_vector_orbit (R := R) Q hfm hf
  have hobs : reducedCoefficientObservationSigma
      {z : Vec d | euclideanNorm z < 33 * R} ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    have heval : Measurable (fun (ω : FieldPair d)
        (x : {z : Vec d | euclideanNorm z < 33 * R}) => ω.1 x) :=
      measurable_pi_lambda _ fun x =>
        ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable
    exact heval.comap_le
  have huambient : Measurable u :=
    hu.comp (measurable_fst.prodMk (measurable_snd.mono le_rfl hobs))
  have havg : @Measurable (FieldPair d) (Vec d)
      (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}) inferInstance
      (fun ω => ∫ y, w y • u (y, ω) ∂ν) := by
    letI : MeasurableSpace (FieldPair d) :=
      reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}
    have hweighted : Measurable
        (fun z : FieldPair d × {y : Vec d // euclideanNorm y ≤ R} =>
          w z.2 • u (z.2, z.1)) :=
      (hwm.comp measurable_snd).smul (hu.comp measurable_swap)
    exact hweighted.stronglyMeasurable.integral_prod_right'.measurable
  exact ⟨u, huambient, hversion, havg,
    local_center_conditioned_euclidean_gradient_bound hR ν hp hA
      w hwm hwi hw0 hw f hf hfm htail u huambient hversion⟩

/-- The local average can be constructed for the production canonical
corrector gradient itself. Its integrability follows from its actual `L²`
class; only the conditional-error estimate remains to be supplied by
Lemma 5.2. Source: `paper/main.tex:968–973`. -/
theorem exists_local_canonical_gradient_average {d : ℕ} {L r₀ R p A : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) (hR : 1 ≤ R)
    (ν : Measure {y : Vec d // euclideanNorm y ≤ R}) [SigmaFinite ν]
    (hp : 1 ≤ p) (hA : 0 ≤ A)
    (w : {y : Vec d // euclideanNorm y ≤ R} → ℝ)
    (hwm : Measurable w) (hwi : Integrable w ν) (hw0 : ∀ y, 0 ≤ w y)
    (hw : (∫ y, w y ∂ν) = 1)
    (htail : let f : FieldPair d → Vec d := fun ω =>
        (StationarySpatialRealization.spatialRealization
          (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
            (reducedEnvironmentLaw Q)) ((0 : Vec d), ω)).ofLp
      eLpNorm (fun ω => euclideanNorm
        (f ω - (reducedEnvironmentLaw Q)[f | reducedCoefficientObservationSigma
          {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A) :
    let f : FieldPair d → Vec d := fun ω =>
      (StationarySpatialRealization.spatialRealization
        (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2
          (reducedEnvironmentLaw Q)) ((0 : Vec d), ω)).ofLp
    ∃ V : FieldPair d → Vec d,
      (@Measurable (FieldPair d) (Vec d)
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})
        inferInstance V) ∧
      MemLp (fun ω => euclideanNorm (V ω - f ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
      eLpNorm (fun ω => euclideanNorm (V ω - f ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal (2 * A) := by
  let G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q) :=
    canonicalCorrectorGradient Q i
  let J := PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)
  have hfm : Measurable (fun ω => J (G ω)) :=
    J.continuous.measurable.comp (Lp.stronglyMeasurable G).measurable
  have hfi : Integrable (fun ω => J (G ω)) (reducedEnvironmentLaw Q) :=
    J.toContinuousLinearMap.integrable_comp ((Lp.memLp G).integrable (by norm_num))
  have htail' : eLpNorm (fun ω => euclideanNorm
      (J (G ω) - (reducedEnvironmentLaw Q)[fun a => J (G a) |
        reducedCoefficientObservationSigma
          {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A := by
    simpa only [StationarySpatialRealization.spatialRealization, translate_zero] using htail
  obtain ⟨u, _, _, hlocal, _, hmem, hb⟩ := exists_local_conditional_gradient_average Q hR ν
    hp hA w hwm hwi hw0 hw (fun ω => J (G ω)) hfi hfm htail'
  refine ⟨fun ω => ∫ y, w y • u (y, ω) ∂ν, hlocal, ?_, ?_⟩
  · simpa only [StationarySpatialRealization.spatialRealization, translate_zero] using hmem
  · simpa only [StationarySpatialRealization.spatialRealization, translate_zero] using hb

end EinsteinRelation.Correctors
