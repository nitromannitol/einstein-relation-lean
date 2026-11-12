import EinsteinRelation.Correctors.LocalMollifierCorrectionIntegrals
import EinsteinRelation.Correctors.LocalScalarCorrectionConstruction
import EinsteinRelation.Correctors.LocalSkewCorrectionConstruction

/-! # The local corrections with the actual mollifier derivative

Source: `paper/main.tex:913–938,942–963`. These constructions instantiate
the derivative weights, including their cancellation, integrability and
uniform inverse-radius bound. The input tail and shift bounds remain
explicit internal obligations for the actual centered correctors.
-/

open MeasureTheory
open scoped ENNReal
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

namespace EinsteinRelation.Correctors
open EinsteinRelation.Entropy

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

private theorem finite_center_volume {d : ℕ} (R : ℝ) :
    IsFiniteMeasure (volume : Measure {y : Vec d // euclideanNorm y ≤ R}) := by
  have hS : MeasurableSet {y : Vec d | euclideanNorm y ≤ R} :=
    (isClosed_le continuous_euclideanNorm' continuous_const).measurableSet
  have hfin : volume {y : Vec d | euclideanNorm y ≤ R} < ⊤ := by
    apply lt_of_le_of_lt (measure_mono (show {y : Vec d | euclideanNorm y ≤ R} ⊆
      Metric.closedBall (0 : Vec d) R from ?_)) (isCompact_closedBall _ _).measure_lt_top
    intro y hy
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_euclideanNorm'' y).trans hy
  exact ⟨(Measure.Subtype.volume_univ hS.nullMeasurableSet).trans_lt hfin⟩

/-- Construct the literal scalar mollifier correction with a weight constant
chosen before the law and radius. Source: `paper/main.tex:913–938,942–963`. -/
theorem exists_local_mollifier_scalar_correction (d : ℕ) :
    ∃ W : ℝ, 0 < W ∧ ∀ {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (_hR : 1 ≤ R)
    {p A B : ℝ} (_hp : 1 ≤ p) (_hA : 0 ≤ A) (_hB : 0 ≤ B)
    (f : FieldPair d → ℝ) (_hfm : Measurable f)
    (_hf : Integrable f (reducedEnvironmentLaw Q))
    (g : Vec d × FieldPair d → ℝ) (_hgm : Measurable g)
    (_hgi : ∀ y, Integrable (fun ω => g (y, ω)) (reducedEnvironmentLaw Q))
    (_hshift : ∀ y : {y : Vec d // euclideanNorm y ≤ R},
      eLpNorm (fun ω => g (y.1, ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
        ENNReal.ofReal B)
    (_htail : eLpNorm (f - (reducedEnvironmentLaw Q)[f |
      reducedCoefficientObservationSigma {z : Vec d | euclideanNorm (z - 0) < 8 * R}])
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A),
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
      (let H : FieldPair d → Vec d := fun ω => ∫ y,
          u (y, ω) • gradient (Calculus.unitMassScaledMollifier d R) (-y.1) ∂volume
       (@Measurable (FieldPair d) (Vec d)
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})
          inferInstance H) ∧
        (∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun y =>
          u (y, ω) • gradient (Calculus.unitMassScaledMollifier d R) (-y.1)) volume) ∧
        MemLp (fun ω => euclideanNorm (H ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
        eLpNorm (fun ω => euclideanNorm (H ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹)) := by
  obtain ⟨W, hW, hweights⟩ := exists_uniform_mollifier_derivative_weights d
  refine ⟨W, hW, ?_⟩
  intro L r₀ R Q hR p A B hp hA hB f hfm hf g hgm hgi hshift htail
  obtain ⟨hwm, hwi, hw, hwbound⟩ := hweights R (zero_lt_one.trans_le hR)
  letI := finite_center_volume (d := d) R
  exact exists_local_scalar_derivative_correction Q hR volume hp hA hB
    (fun y => gradient (Calculus.unitMassScaledMollifier d R) (-y.1))
    hwm hwi hw hwbound f hfm hf g hgm hgi hshift htail

/-- Construct the literal skew mollifier correction with a weight constant
chosen before the law and radius. Source: `paper/main.tex:913–938,942–963`. -/
theorem exists_local_mollifier_skew_correction (d : ℕ) :
    ∃ W : ℝ, 0 < W ∧ ∀ {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (_hR : 1 ≤ R)
    {p A B : ℝ} (_hp : 1 ≤ p) (_hA : 0 ≤ A) (_hB : 0 ≤ B)
    (f : Fin d → FieldPair d → Vec d)
    (_hf : ∀ k, Integrable (f k) (reducedEnvironmentLaw Q))
    (F : Vec d × FieldPair d → Mat d) (_hFm : Measurable F)
    (_hFi : ∀ y k, Integrable (fun ω j => F (y, ω) j k) (reducedEnvironmentLaw Q))
    (_hskew : ∀ y, ∀ᵐ ω ∂reducedEnvironmentLaw Q, (F (y, ω)).transpose = -F (y, ω))
    (_hshift : ∀ k (y : {y : Vec d // euclideanNorm y ≤ R}),
      eLpNorm (fun ω => euclideanNorm ((fun j => F (y.1, ω) j k) - f k ω))
        (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal B)
    (_htail : ∀ k, eLpNorm (fun ω => euclideanNorm (f k ω -
      (reducedEnvironmentLaw Q)[f k | reducedCoefficientObservationSigma
        {z : Vec d | euclideanNorm (z - 0) < 8 * R}] ω))
      (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal A),
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
      (let K : FieldPair d → Vec d := fun ω => ∫ y,
          (S (y, ω)).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (-y.1)) ∂volume
       (@Measurable (FieldPair d) (Vec d)
          (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})
          inferInstance K) ∧
        (∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun y =>
          (S (y, ω)).mulVec (gradient (Calculus.unitMassScaledMollifier d R) (-y.1))) volume) ∧
        MemLp (fun ω => euclideanNorm (K ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ∧
        eLpNorm (fun ω => euclideanNorm (K ω)) (ENNReal.ofReal p) (reducedEnvironmentLaw Q) ≤
          ENNReal.ofReal (((d : ℝ) * (2 * A + B) * W) * R⁻¹)) := by
  obtain ⟨W, hW, hweights⟩ := exists_uniform_mollifier_derivative_weights d
  refine ⟨W, hW, ?_⟩
  intro L r₀ R Q hR p A B hp hA hB f hf F hFm hFi hskew hshift htail
  obtain ⟨hwm, hwi, hw, hwbound⟩ := hweights R (zero_lt_one.trans_le hR)
  letI := finite_center_volume (d := d) R
  exact exists_local_skew_derivative_correction Q hR volume hp hA hB
    (fun y => gradient (Calculus.unitMassScaledMollifier d R) (-y.1))
    hwm hwi hw hwbound f hf F hFm hFi hskew hshift htail

end EinsteinRelation.Correctors
