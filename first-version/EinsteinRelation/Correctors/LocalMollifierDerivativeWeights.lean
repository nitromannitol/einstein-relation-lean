import EinsteinRelation.Entropy.EllipticRegularity
import EinsteinRelation.Correctors.StationarySpatialHorizontal

/-! # Uniform derivative weights for the local mollifier

Source: `paper/main.tex:921-938, 942-963`. The weights are the reflected gradient of the
unit-mass mollifier at radius `R`, restricted to the closed ball of radius `R`. -/

namespace EinsteinRelation.Correctors

open MeasureTheory
open EinsteinRelation.Entropy

attribute [local instance] MeasureTheory.Measure.Subtype.measureSpace

/-- The literal mollifier derivative has cancellation and a uniform inverse-radius L¹ bound.
Source: `paper/main.tex:921–938,942–963`. -/
theorem exists_uniform_mollifier_derivative_weights (d : ℕ) :
    ∃ W : ℝ, 0 < W ∧ ∀ R : ℝ, 0 < R →
      let w : {y : Vec d // euclideanNorm y ≤ R} → Vec d :=
        fun y => gradient (Calculus.unitMassScaledMollifier d R) (-y.1)
      Measurable w ∧
        (∀ j : Fin d, Integrable (fun y => w y j) volume) ∧
        (∀ j : Fin d, (∫ y, w y j) = 0) ∧
        (∀ j : Fin d, (∫ y, |w y j|) ≤ W * R⁻¹) := by
  have hB : ∀ k : Fin d, 0 ≤ ∫ u, |coordinateDerivative k (mollifier d) u| :=
    fun k => integral_nonneg fun u => abs_nonneg _
  have hBsum : 0 ≤ ∑ k : Fin d, ∫ u, |coordinateDerivative k (mollifier d) u| :=
    Finset.sum_nonneg fun k _ => hB k
  refine ⟨1 + ∑ k : Fin d, ∫ u, |coordinateDerivative k (mollifier d) u|, by linarith, ?_⟩
  intro R hR
  dsimp only
  have hζs := contDiff_unitMassScaledMollifier (d := d) R
  have hcont := fun j : Fin d =>
    continuous_coordinateDerivative_unitMassScaledMollifier (d := d) R j
  have hζc := hasCompactSupport_unitMassScaledMollifier (d := d) hR
  -- the closed-ball set and its compact envelope
  have hS : MeasurableSet {y : Vec d | euclideanNorm y ≤ R} :=
    (isClosed_le continuous_euclideanNorm' continuous_const).measurableSet
  have hsubset : {y : Vec d | euclideanNorm y ≤ R} ⊆ Metric.closedBall (0 : Vec d) R := by
    intro y hy
    have hy' : euclideanNorm y ≤ R := hy
    rw [Metric.mem_closedBall, dist_zero_right]
    exact (norm_le_euclideanNorm'' y).trans hy'
  have hloc : ∀ j : Fin d, IntegrableOn
      (fun x : Vec d => coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-x))
      {y : Vec d | euclideanNorm y ≤ R} volume := fun j =>
    (((hcont j).comp continuous_neg).continuousOn.integrableOn_compact
      (isCompact_closedBall (0 : Vec d) R)).mono_set hsubset
  -- the reflected derivative vanishes outside the ball
  have hzero_out : ∀ j : Fin d, ∀ x : Vec d, x ∉ {y : Vec d | euclideanNorm y ≤ R} →
      coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-x) = 0 := by
    intro j x hx
    have hx' : ¬ euclideanNorm x ≤ R := hx
    have hfar : R < euclideanNorm (-x) := by
      have hn : euclideanNorm (-x) = euclideanNorm x := by
        simp [euclideanNorm, euclideanSq, dot]
      rw [hn]
      exact not_le.mp hx'
    exact coordinateDerivative_unitMassScaledMollifier_eq_zero hR j hfar
  have hint_zero : ∀ j : Fin d,
      (∫ x, coordinateDerivative j (Calculus.unitMassScaledMollifier d R) x) = 0 :=
    fun j => integral_coordinateDerivative_eq_zero hζs hζc j
  have hmeas : Measurable (fun y : {y : Vec d // euclideanNorm y ≤ R} =>
      gradient (Calculus.unitMassScaledMollifier d R) (-y.1)) := by
    refine measurable_pi_lambda _ fun j => ?_
    exact ((hcont j).comp continuous_neg).measurable.comp measurable_subtype_coe
  have hsub : ∀ j : Fin d, Integrable (fun y : {y : Vec d // euclideanNorm y ≤ R} =>
      gradient (Calculus.unitMassScaledMollifier d R) (-y.1) j) volume := fun j =>
    (integrableOn_iff_comap_subtypeVal hS).mp (hloc j)
  have hzero : ∀ j : Fin d, (∫ y : {y : Vec d // euclideanNorm y ≤ R},
      gradient (Calculus.unitMassScaledMollifier d R) (-y.1) j) = 0 := by
    intro j
    calc (∫ y : {y : Vec d // euclideanNorm y ≤ R},
            gradient (Calculus.unitMassScaledMollifier d R) (-y.1) j)
        = ∫ y : {y : Vec d // euclideanNorm y ≤ R},
            coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y.1) := rfl
      _ = ∫ x in {y : Vec d | euclideanNorm y ≤ R},
            coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-x) :=
          integral_subtype hS
            (fun x : Vec d => coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-x))
      _ = ∫ x, coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-x) :=
          setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => hzero_out j x hx
      _ = ∫ x, coordinateDerivative j (Calculus.unitMassScaledMollifier d R) x :=
          integral_neg_eq_self (coordinateDerivative j (Calculus.unitMassScaledMollifier d R)) volume
      _ = 0 := hint_zero j
  have hL1 : ∀ j : Fin d, (∫ y : {y : Vec d // euclideanNorm y ≤ R},
      |gradient (Calculus.unitMassScaledMollifier d R) (-y.1) j|) =
      R⁻¹ * ∫ u, |coordinateDerivative j (mollifier d) u| := by
    intro j
    calc (∫ y : {y : Vec d // euclideanNorm y ≤ R},
            |gradient (Calculus.unitMassScaledMollifier d R) (-y.1) j|)
        = ∫ y : {y : Vec d // euclideanNorm y ≤ R},
            |coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y.1)| := rfl
      _ = ∫ x in {y : Vec d | euclideanNorm y ≤ R},
            |coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-x)| :=
          integral_subtype hS
            (fun x : Vec d => |coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-x)|)
      _ = ∫ x, |coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-x)| :=
          setIntegral_eq_integral_of_forall_compl_eq_zero fun x hx => by
            simp only [hzero_out j x hx, abs_zero]
      _ = ∫ x, |coordinateDerivative j (Calculus.unitMassScaledMollifier d R) x| :=
          integral_neg_eq_self
            (fun x => |coordinateDerivative j (Calculus.unitMassScaledMollifier d R) x|) volume
      _ = R⁻¹ * ∫ u, |coordinateDerivative j (mollifier d) u| :=
          integral_abs_coordinateDerivative_unitMassScaledMollifier hR j
  refine ⟨hmeas, hsub, hzero, fun j => ?_⟩
  have hBj : (∫ u, |coordinateDerivative j (mollifier d) u|) ≤
      ∑ k : Fin d, ∫ u, |coordinateDerivative k (mollifier d) u| :=
    Finset.single_le_sum (fun k _ => hB k) (Finset.mem_univ j)
  have hle : (∫ u, |coordinateDerivative j (mollifier d) u|) ≤
      1 + ∑ k : Fin d, ∫ u, |coordinateDerivative k (mollifier d) u| := by
    linarith
  have hRinv : 0 ≤ R⁻¹ := inv_nonneg.mpr hR.le
  rw [hL1 j]
  exact (mul_le_mul_of_nonneg_left hle hRinv).trans_eq (mul_comm _ _)

end EinsteinRelation.Correctors
