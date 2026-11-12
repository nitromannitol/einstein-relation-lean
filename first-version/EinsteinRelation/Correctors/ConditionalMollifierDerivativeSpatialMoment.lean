import EinsteinRelation.Correctors.CorrectorBallSourceMomentsFromLiterature
import EinsteinRelation.Correctors.ConditionalSpatialWeightedMoment
import EinsteinRelation.Correctors.ConditionalSpatialProductMoment

/-! # Derivative averages from ordinary spatial source moments

Source: `paper/main.tex:921–925,942–947`. Rescaled mollifier derivatives
are bounded weights for normalized ball volume. This gives the literal
full-space correction estimates from joint source moments.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open Entropy External.AKM
open EinsteinRelation.Carriers (reducedCoefficientObservationSigma)

local instance {d : ℕ} : StandardBorelSpace (FieldPair d) :=
  ReductionImageV3.fieldPair_standardBorel d

/-- The derivative-weight integral against normalized ball volume is the
literal full-space mollifier derivative integral.
Source: `paper/main.tex:921–925`. -/
theorem integral_correctorBallMeasure_derivative_weight {d : ℕ} {R : ℝ}
    (hR : 0 < R) (j : Fin d) (f : Vec d → ℝ) :
    (∫ y, (volume.real (ball (0 : Vec d) (2 * R)) *
      coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y)) * f y
      ∂correctorBallMeasure d R) =
      ∫ y, f y * coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y) := by
  have hv := paired_ball_volume_pos_finite (d := d) (show 0 < 2 * R by positivity)
  rw [correctorBallMeasure, integral_smul_measure, ENNReal.toReal_inv]
  simp only [mul_assoc, integral_const_mul, smul_eq_mul, Measure.real]
  change 0 < (volume (ball (0 : Vec d) (2 * R))).toReal at hv
  rw [← mul_assoc, inv_mul_cancel₀ hv.ne', one_mul]
  rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
  · congr 1
    funext y
    exact mul_comm _ _
  · intro y hy
    have hn : 2 * R ≤ euclideanNorm y := by
      simpa only [ball, Set.mem_setOf_eq, sub_zero, not_lt] using hy
    rw [coordinateDerivative_unitMassScaledMollifier_eq_zero hR j
      (by rw [euclideanNorm_neg']; linarith), zero_mul]

/-- Normalized-volume derivative weights have a uniform inverse-radius
pointwise bound. Source: `paper/main.tex:942–947`. -/
theorem exists_uniform_ball_mollifier_derivative_bound (d : ℕ) :
    ∃ W : ℝ, 0 < W ∧ ∀ (R : ℝ), 0 < R → ∀ (j : Fin d) (y : Vec d),
      |volume.real (ball (0 : Vec d) (2 * R)) *
        coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y)| ≤ W * R⁻¹ := by
  have hb (j : Fin d) :=
    (hasCompactSupport_coordinateDerivative_unitMassScaledMollifier
      (d := d) (δ := 1) zero_lt_one j).exists_bound_of_continuous
      (continuous_coordinateDerivative_unitMassScaledMollifier 1 j)
  choose M hM using hb
  let A : ℝ := 1 + ∑ j : Fin d, |M j|
  have hA : 0 < A := by dsimp only [A]; positivity
  have hbase (j : Fin d) (x : Vec d) : |coordinateDerivative j (mollifier d) x| ≤ A := by
    have hx := hM j x
    simp only [coordinateDerivative_unitMassScaledMollifier, one_pow, inv_one,
      one_mul, one_smul, Real.norm_eq_abs] at hx
    have hs := Finset.single_le_sum (fun k _ => abs_nonneg (M k)) (Finset.mem_univ j)
    dsimp only [A]
    linarith [le_abs_self (M j)]
  let V := volume.real (ball (0 : Vec d) 1)
  have hV : 0 < V := paired_ball_volume_pos_finite (d := d) zero_lt_one
  refine ⟨2 ^ d * V * A, by positivity, ?_⟩
  intro R hR j y
  have hv := paired_ball_volume_pos_finite (d := d) (show 0 < 2 * R by positivity)
  rw [abs_mul, abs_of_pos hv, coordinateDerivative_unitMassScaledMollifier,
    abs_mul, abs_mul, abs_of_pos (inv_pos.mpr (pow_pos hR _)), abs_of_pos (inv_pos.mpr hR)]
  calc
    _ ≤ volume.real (ball (0 : Vec d) (2 * R)) * ((R ^ d)⁻¹ * R⁻¹ * A) :=
      mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left (hbase j _) (by positivity)) hv.le
    _ = _ := by
      rw [paired_ball_volume_real (by positivity : 0 < 2 * R), mul_pow]
      dsimp only [V]
      field_simp

/-- A literal conditional derivative average is bounded by the joint
ordinary spatial source norm. Source: `paper/main.tex:942–947`. -/
theorem eLpNorm_conditional_mollifier_derivative_le_spatial_moment (d : ℕ) :
    ∃ W : ℝ, 0 < W ∧ ∀ {L r₀ R : ℝ} (Q : EnvironmentLaw d L r₀)
      (_hR : 0 < R) {p : ℝ≥0∞} (_hp : 1 ≤ p) (_hpt : p ≠ ∞)
      (u : FieldPair d → Vec d → ℝ) (_hum : StronglyMeasurable (Function.uncurry u))
      (_hu : MemLp (fun z : FieldPair d × Vec d => u z.1 (-z.2)) p
        ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R))) (j : Fin d),
      eLpNorm (fun ω => ∫ y, conditionalSpatialAverage
          (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
          (reducedEnvironmentLaw Q) u (translate y ω) (-y) *
          coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y)) p
        (reducedEnvironmentLaw Q) ≤
        ENNReal.ofReal (W * R⁻¹) * eLpNorm
          (fun z : FieldPair d × Vec d => u z.1 (-z.2)) p
          ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R)) := by
  obtain ⟨W, hW, hb⟩ := exists_uniform_ball_mollifier_derivative_bound d
  refine ⟨W, hW, ?_⟩
  intro L r₀ R Q hR p hp hpt u hum hu j
  letI := isProbabilityMeasure_correctorBallMeasure (d := d) hR
  have hw : Measurable (fun y : Vec d => volume.real (ball (0 : Vec d) (2 * R)) *
      coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y)) :=
    ((continuous_coordinateDerivative_unitMassScaledMollifier R j).measurable.comp
      measurable_neg).const_mul _
  have h := eLpNorm_integral_weight_centered_conditionalSpatialAverage_le
    (R := R) Q (correctorBallMeasure d R) hp hpt _ hw
    (ae_of_all _ (hb R hR j)) u hum hu
  simp_rw [integral_correctorBallMeasure_derivative_weight hR j] at h
  exact h

/-- Joint source moments give the ordinary section integrability needed to
expand skew derivative integrals into a finite sum, almost surely.
Source: `paper/main.tex:921–925,942–947`. -/
theorem ae_integrable_conditional_mollifier_derivative {d : ℕ} {L r₀ R : ℝ}
    (Q : EnvironmentLaw d L r₀) (hR : 0 < R) {p : ℝ≥0∞}
    (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (u : FieldPair d → Vec d → ℝ) (hum : StronglyMeasurable (Function.uncurry u))
    (hu : MemLp (fun z : FieldPair d × Vec d => u z.1 (-z.2)) p
      ((reducedEnvironmentLaw Q).prod (correctorBallMeasure d R))) (j : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, Integrable (fun y => conditionalSpatialAverage
      (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
      (reducedEnvironmentLaw Q) u (translate y ω) (-y) *
      coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y)) volume := by
  letI := isProbabilityMeasure_correctorBallMeasure (d := d) hR
  have hm := (memLp_centered_conditionalSpatialAverage_product (R := R)
    Q (correctorBallMeasure d R) hp hpt u hum hu).1
  obtain ⟨M, hM⟩ := (hasCompactSupport_coordinateDerivative_unitMassScaledMollifier hR j).exists_bound_of_continuous (continuous_coordinateDerivative_unitMassScaledMollifier R j)
  have hvol := ENNReal.toReal_pos_iff.mp
    (paired_ball_volume_pos_finite (d := d) (show 0 < 2 * R by positivity))
  filter_upwards [(hm.integrable hp).prod_right_ae] with ω hω
  have hb := hω.mul_bdd
    (((continuous_coordinateDerivative_unitMassScaledMollifier R j).comp
      continuous_neg).measurable.aestronglyMeasurable)
    (ae_of_all _ (fun y => hM (-y)))
  have hi : IntegrableOn (fun y => conditionalSpatialAverage
      (reducedCoefficientObservationSigma {x : Vec d | euclideanNorm x < 32 * R})
      (reducedEnvironmentLaw Q) u (translate y ω) (-y) *
      coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (-y))
      (ball (0 : Vec d) (2 * R)) volume :=
    (integrable_inv_smul_measure hvol.1.ne' hvol.2.ne).mp hb
  apply hi.integrable_of_forall_notMem_eq_zero
  intro y hy
  have hn : 2 * R ≤ euclideanNorm y := by
    simpa only [ball, Set.mem_setOf_eq, sub_zero, not_lt] using hy
  rw [coordinateDerivative_unitMassScaledMollifier_eq_zero hR j
    (by rw [euclideanNorm_neg']; linarith), mul_zero]

end EinsteinRelation.Correctors
