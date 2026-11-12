import EinsteinRelation.Correctors.JointCenterConditionalFamily
import EinsteinRelation.Correctors.LocalScalarDerivativeCorrection

/-! # Constructing the scalar derivative correction

Source: `paper/main.tex:913–938,942–963`. Moving-window conditional
fields are constructed from the given centered observables. Cancellation
then bounds their literal weight-derivative integral. Joint local versions
and a derivative-correction estimate are conclusions of the construction.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- Construct the scalar conditional field and its locally measurable
derivative correction from the centered tail and shifted mean bounds.
Source: `paper/main.tex:913–938,948–963`. -/
theorem exists_local_scalar_derivative_correction {d : ℕ} {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (hR : 1 ≤ R)
    (ν : Measure {y : Vec d // euclideanNorm y ≤ R}) [SigmaFinite ν]
    {p A B W : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : {y : Vec d // euclideanNorm y ≤ R} → Vec d) (hwm : Measurable w)
    (hwi : ∀ j, Integrable (fun y => w y j) ν)
    (hw : ∀ j, (∫ y, w y j ∂ν) = 0)
    (hwbound : ∀ j, (∫ y, |w y j| ∂ν) ≤ W * R⁻¹)
    (f : FieldPair d → ℝ) (hfm : Measurable f)
    (hf : Integrable f (reducedEnvironmentLaw Q))
    (g : Vec d × FieldPair d → ℝ) (hgm : Measurable g)
    (hgi : ∀ y, Integrable (fun ω => g (y, ω)) (reducedEnvironmentLaw Q))
    (hshift : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      eLpNorm (fun ω => g (y.1, ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
        ENNReal.ofReal B)
    (htail : eLpNorm (f - (reducedEnvironmentLaw Q)[f |
      reducedCoefficientObservationSigma {z : Vec d | euclideanNorm (z - 0) < 8 * R}])
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A) :
    ∃ u : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → ℝ,
      (@Measurable ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d) ℝ
        (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}))
        inferInstance u) ∧
      (∀ y : {y : Vec d // euclideanNorm y ≤ R},
        (fun ω => u (y, ω)) =ᵐ[reducedEnvironmentLaw Q]
          (reducedEnvironmentLaw Q)[fun ω => f ω + g (y.1, ω) |
            reducedCoefficientObservationSigma
              {z | euclideanNorm (z - y.1) < 32 * R}]) ∧
      (let H : FieldPair d → Vec d := fun ω => ∫ y, u (y, ω) • w y ∂ν
       (@Measurable (FieldPair d) (Vec d)
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})
          inferInstance H) ∧
        (∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun y => u (y, ω) • w y) ν) ∧
        MemLp (fun ω => euclideanNorm (H ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
        eLpNorm (fun ω => euclideanNorm (H ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹)) := by
  obtain ⟨u, hum, huv⟩ := exists_joint_center_conditioned_family Q
    (fun z => f z.2 + g z) ((hfm.comp measurable_snd).add hgm)
    (fun y => hf.add (hgi y))
  have hle : reducedCoefficientObservationSigma
      {z : Vec d | euclideanNorm z < 33 * R} ≤ borel (FieldPair d) := by
    rw [reducedCoefficientObservationSigma_eq_comap_evaluation]
    exact (measurable_pi_lambda _ fun x : {z : Vec d // euclideanNorm z < 33 * R} =>
      ((continuous_eval_const (x : Vec d)).comp continuous_fst).measurable).comap_le
  have hui : @Measurable
      ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d)
      ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d)
      inferInstance
      (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})) id :=
    measurable_fst.prodMk ((measurable_id'' hle).comp measurable_snd)
  have hu : Measurable u := hum.comp hui
  have hbound := local_center_conditioned_scalar_derivative_bound hR ν hp hA hB
    w hwm hwi hw hwbound f hf (fun y ω => g (y.1, ω))
    (fun y => hgi y.1) hshift htail u hu huv
  refine ⟨u, hum, huv, ?_, hbound.1, hbound.2.2⟩
  letI : MeasurableSpace (FieldPair d) :=
    reducedCoefficientObservationSigma {z : Vec d | euclideanNorm z < 33 * R}
  have hm : Measurable (fun z => u z • w z.1) := hum.smul (hwm.comp measurable_fst)
  exact (hm.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable

end EinsteinRelation.Correctors
