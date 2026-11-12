import EinsteinRelation.Correctors.CenteredMollifierFields
import EinsteinRelation.Correctors.LocalCenterObservation
import EinsteinRelation.Correctors.LocalMollifierDerivativeWeights
import EinsteinRelation.Correctors.WeightedLocalFlux

/-! # Locality of the common five center averages

Source: `paper/main.tex:921–938`. Joint center-zero coefficient locality
and the literal mollifier support give radius-33R locality for every
field, including both derivative corrections.
-/

open MeasureTheory
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)
open EinsteinRelation.TimeChange

namespace EinsteinRelation.Correctors

/-- A supported joint local observable can be integrated over all centers
using only coefficients in the radius-33R ball.
Source: `paper/main.tex:931–938`. -/
theorem measurable_supported_local_center_integral {d : ℕ} (R : ℝ)
    (F : Vec d → FieldPair d → ℝ)
    (hF : @Measurable (Vec d × FieldPair d) ℝ
      (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 32 * R}))
      inferInstance (Function.uncurry F))
    (hzero : ∀ x, R < euclideanNorm x → ∀ ω, F x ω = 0) :
    Measurable[reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}]
      (fun ω => ∫ y, F (-y) (translate y ω)) := by
  let B : Set (Vec d) := {y | euclideanNorm y ≤ R}
  have hB : MeasurableSet B :=
    (isClosed_le Entropy.continuous_euclideanNorm' continuous_const).measurableSet
  have hBW : ∀ y ∈ B, ∀ z : Vec d, euclideanNorm z < 32 * R →
      euclideanNorm (y + z) < 33 * R := by
    intro y hy z hz
    have ht := euclideanNorm_add_le y z
    change euclideanNorm y ≤ R at hy
    linarith
  have hm := measurable_centered_local_observable (S := B)
    (U := {z | euclideanNorm z < 32 * R})
    (W := {z | euclideanNorm z < 33 * R}) hBW F hF (0 : Vec d)
  have hi := @measurable_setIntegral_of_measurable_subtype (Vec d) (FieldPair d) ℝ
    inferInstance (reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R})
    _ _ _ _ _ _ volume _ B hB (fun y ω => F (-y) (translate y ω))
    (by simpa only [zero_sub] using hm)
  have heq (ω : FieldPair d) : (∫ y in B, F (-y) (translate y ω)) =
      ∫ y, F (-y) (translate y ω) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro y hy
    apply hzero
    have hn : euclideanNorm (-y) = euclideanNorm y := by
      simp [euclideanNorm, euclideanSq, dot]
    rw [hn]
    exact not_le.mp hy
  simpa only [heq] using hi

/-- All five literal center averages are coefficient-local before any
moment or weak-equation estimate is imposed.
Source: `paper/main.tex:921–938`. -/
theorem measurable_centeredMollifierFields {d : ℕ} {R : ℝ} (hR : 0 < R)
    (u : FieldPair d → Vec d → ℝ) (G : FieldPair d → Vec d → Vec d)
    (S : FieldPair d → Vec d → Mat d)
    (hu : @Measurable (Vec d × FieldPair d) ℝ
      (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 32 * R})) _
      (fun z => u z.2 z.1))
    (hG : ∀ j, @Measurable (Vec d × FieldPair d) ℝ
      (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 32 * R})) _
      (fun z => G z.2 z.1 j))
    (hS : ∀ j k, @Measurable (Vec d × FieldPair d) ℝ
      (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 32 * R})) _
      (fun z => S z.2 z.1 j k)) :
    let f := centeredMollifierFields R u G S
    let obs := reducedCoefficientObservationSigma {z | euclideanNorm z < 33 * R}
    Measurable[obs] f.scalar ∧ Measurable[obs] f.skew ∧
      Measurable[obs] f.gradientAverage ∧ Measurable[obs] f.scalarCorrection ∧
      Measurable[obs] f.skewCorrection := by
  let obs := reducedCoefficientObservationSigma {z : Vec d | euclideanNorm z < 33 * R}
  have hw : @Measurable (Vec d × FieldPair d) ℝ
      (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 32 * R})) _
      (fun z => Calculus.unitMassScaledMollifier d R z.1) :=
    (Entropy.contDiff_unitMassScaledMollifier R).continuous.measurable.comp measurable_fst
  have hD (j : Fin d) : @Measurable (Vec d × FieldPair d) ℝ
      (@Prod.instMeasurableSpace (Vec d) (FieldPair d) _
        (reducedCoefficientObservationSigma {z | euclideanNorm z < 32 * R})) _
      (fun z => coordinateDerivative j (Calculus.unitMassScaledMollifier d R) z.1) :=
    (Entropy.continuous_coordinateDerivative_unitMassScaledMollifier R j).measurable.comp
      measurable_fst
  have hwzero (x : Vec d) (hx : R < euclideanNorm x) :
      Calculus.unitMassScaledMollifier d R x = 0 := by
    by_contra hn
    exact (not_lt_of_ge hx.le)
      (Entropy.euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero hR hn)
  have hDzero (j : Fin d) (x : Vec d) (hx : R < euclideanNorm x) :=
    Entropy.coordinateDerivative_unitMassScaledMollifier_eq_zero hR j hx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact measurable_supported_local_center_integral R
      (fun x ω => Calculus.unitMassScaledMollifier d R x * u ω x) (hw.mul hu)
      (fun x hx ω => by simp only [hwzero x hx, zero_mul])
  · have hm : @Measurable (FieldPair d) (Fin d → Fin d → ℝ) obs MeasurableSpace.pi
        (centeredMollifierFields R u G S).skew := by
      refine measurable_pi_lambda _ fun j => measurable_pi_lambda _ fun k => ?_
      exact measurable_supported_local_center_integral R
        (fun x ω => Calculus.unitMassScaledMollifier d R x * S ω x j k) (hw.mul (hS j k))
        (fun x hx ω => by simp only [hwzero x hx, zero_mul])
    exact hm.mono le_rfl (OpensMeasurableSpace.borel_le (α := Fin d → Fin d → ℝ))
  · refine measurable_pi_lambda _ fun j => ?_
    exact measurable_supported_local_center_integral R
      (fun x ω => Calculus.unitMassScaledMollifier d R x * G ω x j) (hw.mul (hG j))
      (fun x hx ω => by simp only [hwzero x hx, zero_mul])
  · refine measurable_pi_lambda _ fun j => ?_
    exact measurable_supported_local_center_integral R
      (fun x ω => u ω x * coordinateDerivative j (Calculus.unitMassScaledMollifier d R) x)
      (hu.mul (hD j)) (fun x hx ω => by simp only [hDzero j x hx, mul_zero])
  · refine measurable_pi_lambda _ fun j => ?_
    apply measurable_supported_local_center_integral R
      (fun x ω => ((S ω x).mulVec (gradient (Calculus.unitMassScaledMollifier d R) x)) j)
    · simpa only [Function.uncurry, Matrix.mulVec, dotProduct, gradient] using
        (Finset.measurable_fun_sum Finset.univ fun k _ => (hS j k).mul (hD k))
    · intro x hx ω
      change (∑ k : Fin d, S ω x j k *
        coordinateDerivative k (Calculus.unitMassScaledMollifier d R) x) = 0
      simp only [hDzero _ x hx, mul_zero, Finset.sum_const_zero]

/-- Pointwise skewness is preserved by the same full-space center average.
Source: `paper/main.tex:921–938`. -/
theorem centeredMollifierFields_skew {d : ℕ} (R : ℝ)
    (u : FieldPair d → Vec d → ℝ) (G : FieldPair d → Vec d → Vec d)
    (S : FieldPair d → Vec d → Mat d) (hS : ∀ ω x, (S ω x).transpose = -(S ω x))
    (ω : FieldPair d) :
    ((centeredMollifierFields R u G S).skew ω).transpose =
      -(centeredMollifierFields R u G S).skew ω :=
  integral_weight_skew volume (fun y => Calculus.unitMassScaledMollifier d R (-y))
    (fun y => S (translate y ω) (-y)) (fun y => hS (translate y ω) (-y))

end EinsteinRelation.Correctors
