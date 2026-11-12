import EinsteinRelation.Correctors.JointCenterConditionalSkewFamily
import EinsteinRelation.Correctors.LocalSkewDerivativeCorrection

/-! # Constructing the skew derivative correction

Source: `paper/main.tex:913–938,942–963`. Moving-window conditional
fields are constructed from the given centered observables. Cancellation
then bounds their literal weight-derivative integral. Joint local versions
and a derivative-correction estimate are conclusions of the construction.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors

/-- Construct the skew conditional field and its locally measurable
derivative correction from the centered tail and shifted mean bounds.
Source: `paper/main.tex:913–938,948–963`. -/
theorem exists_local_skew_derivative_correction {d : ℕ} {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (hR : 1 ≤ R)
    (ν : Measure {y : Vec d // euclideanNorm y ≤ R}) [SigmaFinite ν]
    {p A B W : ℝ} (hp : 1 ≤ p) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (w : {y : Vec d // euclideanNorm y ≤ R} → Vec d) (hwm : Measurable w)
    (hwi : ∀ j, Integrable (fun y => w y j) ν)
    (hw : ∀ j, (∫ y, w y j ∂ν) = 0)
    (hwbound : ∀ j, (∫ y, |w y j| ∂ν) ≤ W * R⁻¹)
    (f : Fin d → FieldPair d → Vec d)
    (hf : ∀ k, Integrable (f k) (reducedEnvironmentLaw Q))
    (F : Vec d × FieldPair d → Mat d) (hFm : Measurable F)
    (hFi : ∀ y k, Integrable (fun ω j => F (y, ω) j k) (reducedEnvironmentLaw Q))
    (hskew : ∀ y, ∀ᵐ ω ∂reducedEnvironmentLaw Q, (F (y, ω)).transpose = -F (y, ω))
    (hshift : ∀ k (y : {y : Vec d // euclideanNorm y ≤ R}),
      eLpNorm (fun ω => euclideanNorm ((fun j => F (y.1, ω) j k) - f k ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal B)
    (htail : ∀ k, eLpNorm (fun ω => euclideanNorm (f k ω -
      (reducedEnvironmentLaw Q)[f k | reducedCoefficientObservationSigma
        {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A) :
    ∃ S : {y : Vec d // euclideanNorm y ≤ R} × FieldPair d → Mat d,
      (@Measurable ({y : Vec d // euclideanNorm y ≤ R} × FieldPair d) (Mat d)
        (@Prod.instMeasurableSpace {y : Vec d // euclideanNorm y ≤ R} (FieldPair d) _
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}))
        inferInstance S) ∧
      (∀ z, (S z).transpose = -S z) ∧
      (∀ k (y : {y : Vec d // euclideanNorm y ≤ R}),
        (fun ω j => S (y, ω) j k) =ᵐ[reducedEnvironmentLaw Q]
          (reducedEnvironmentLaw Q)[fun ω j => F (y.1, ω) j k |
            reducedCoefficientObservationSigma
              {z | euclideanNorm (z - y.1) < 32 * R}]) ∧
      (let K : FieldPair d → Vec d := fun ω => ∫ y, (S (y, ω)).mulVec (w y) ∂ν
       (@Measurable (FieldPair d) (Vec d)
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})
          inferInstance K) ∧
        (∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun y => (S (y, ω)).mulVec (w y)) ν) ∧
        MemLp (fun ω => euclideanNorm (K ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
        eLpNorm (fun ω => euclideanNorm (K ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹)) := by
  obtain ⟨S, hSm, hSs, hSv⟩ :=
    exists_joint_center_conditioned_skew_family Q R F hFm hFi hskew
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
  have hS : Measurable S := hSm.comp hui
  let g : Fin d → {y : Vec d // euclideanNorm y ≤ R} → FieldPair d → Vec d :=
    fun k y ω => (fun j => F (y.1, ω) j k) - f k ω
  have hgi (k : Fin d) (y : {y : Vec d // euclideanNorm y ≤ R}) :
      Integrable (g k y) (reducedEnvironmentLaw Q) := (hFi y.1 k).sub (hf k)
  have hversion (k : Fin d) (y : {y : Vec d // euclideanNorm y ≤ R}) :
      (fun ω j => S (y, ω) j k) =ᵐ[reducedEnvironmentLaw Q]
        (reducedEnvironmentLaw Q)[f k + g k y | reducedCoefficientObservationSigma
          {z | euclideanNorm (z - y.1) < 32 * R}] := by
    have heq : f k + g k y = fun ω j => F (y.1, ω) j k := by
      ext ω j
      dsimp only [g, Pi.add_apply, Pi.sub_apply]
      ring
    rw [heq]
    exact hSv k y
  have hbound := local_center_conditioned_skew_derivative_bound hR ν hp hA hB
    w hwm hwi hw hwbound f hf g hgi hshift htail S hS hversion
  refine ⟨S, hSm, hSs, hSv, ?_, hbound.1, hbound.2.2⟩
  letI : MeasurableSpace (FieldPair d) :=
    reducedCoefficientObservationSigma {z : Vec d | euclideanNorm z < 33 * R}
  have hm : Measurable (fun z => (S z).mulVec (w z.1)) := by
    apply measurable_pi_lambda
    intro j
    change Measurable (fun z => ∑ k : Fin d, S z j k * w z.1 k)
    exact Finset.measurable_fun_sum _ fun k _ =>
      ((continuous_id.matrix_elem j k).measurable.comp hSm).mul
        (((measurable_pi_apply k).comp hwm).comp measurable_fst)
  exact (hm.comp measurable_swap).stronglyMeasurable.integral_prod_right'.measurable

end EinsteinRelation.Correctors
