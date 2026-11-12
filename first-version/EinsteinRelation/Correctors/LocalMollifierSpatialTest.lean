import EinsteinRelation.Entropy.EllipticRegularity
import EinsteinRelation.Correctors.SpatialWeakLocalization

/-! # Translated smooth mollifiers as spatial tests

Source: `paper/main.tex:913–938`. A unit-mass mollifier at scale `R`, centred at
`y`, is a spatial test for the local conditioning ball of radius `32 R` about
`y`. Its coordinate derivatives translate with the same displacement.

Uses the mollifier helpers `contDiff_unitMassScaledMollifier`,
`hasCompactSupport_unitMassScaledMollifier`, and
`euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero`, and `continuous_euclideanNorm'`.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open Entropy

/-- A translated unit-mass mollifier is a spatial test for the ball of radius
`32 R` about its centre. Source: `paper/main.tex:913–938`. -/
theorem isSpatialTest_translated_unitMassScaledMollifier {d : ℕ} {R : ℝ} (hR : 0 < R)
    (y : Vec d) :
    IsSpatialTest {x : Vec d | euclideanNorm (x - y) < 32 * R}
      (fun x => Calculus.unitMassScaledMollifier d R (x - y)) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (Calculus.unitMassScaledMollifier d R) :=
    contDiff_unitMassScaledMollifier R
  have hcs : HasCompactSupport (Calculus.unitMassScaledMollifier d R) :=
    hasCompactSupport_unitMassScaledMollifier hR
  have hsupp : tsupport (Calculus.unitMassScaledMollifier d R) ⊆
      {z : Vec d | euclideanNorm z ≤ R} := by
    refine closure_minimal (fun z hz => ?_)
      (isClosed_le continuous_euclideanNorm' continuous_const)
    exact (euclideanNorm_lt_of_unitMassScaledMollifier_ne_zero hR hz).le
  refine ⟨hcd.comp (contDiff_id.sub contDiff_const), ?_, ?_⟩
  · simpa only [Function.comp_def, sub_eq_add_neg] using
      hcs.comp_homeomorph (Homeomorph.addRight (-y))
  · intro x hx
    have hx' : x - y ∈ tsupport (Calculus.unitMassScaledMollifier d R) :=
      tsupport_comp_subset_preimage (Calculus.unitMassScaledMollifier d R)
        (continuous_id.sub continuous_const) hx
    have hle : euclideanNorm (x - y) ≤ R := hsupp hx'
    show euclideanNorm (x - y) < 32 * R
    linarith

/-- The coordinate derivative of a translated unit-mass mollifier is the coordinate
derivative of the mollifier at the translated point. Source: `paper/main.tex:913–938`. -/
theorem coordinateDerivative_translated_unitMassScaledMollifier {d : ℕ} (R : ℝ)
    (x y : Vec d) (j : Fin d) :
    coordinateDerivative j (fun z => Calculus.unitMassScaledMollifier d R (z - y)) x =
      coordinateDerivative j (Calculus.unitMassScaledMollifier d R) (x - y) := by
  have hcd : ContDiff ℝ (⊤ : ℕ∞) (Calculus.unitMassScaledMollifier d R) :=
    contDiff_unitMassScaledMollifier R
  have hdiff : DifferentiableAt ℝ (Calculus.unitMassScaledMollifier d R) (x - y) :=
    hcd.differentiable (mod_cast le_top) (x - y)
  have hlin : HasFDerivAt (fun z : Vec d => z - y) (ContinuousLinearMap.id ℝ (Vec d)) x :=
    (hasFDerivAt_id x).sub_const y
  have h : HasFDerivAt (fun z : Vec d => Calculus.unitMassScaledMollifier d R (z - y))
      ((fderiv ℝ (Calculus.unitMassScaledMollifier d R) (x - y)).comp
        (ContinuousLinearMap.id ℝ (Vec d))) x :=
    HasFDerivAt.comp (f := fun z : Vec d => z - y)
      (g := Calculus.unitMassScaledMollifier d R) x hdiff.hasFDerivAt hlin
  show fderiv ℝ (fun z => Calculus.unitMassScaledMollifier d R (z - y)) x (unitVector j) =
    fderiv ℝ (Calculus.unitMassScaledMollifier d R) (x - y) (unitVector j)
  rw [h.fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply]

/-- The translated weight has exactly the gradient used in the scalar and
skew correction integrals. Source: `paper/main.tex:921–938`. -/
theorem gradient_translated_unitMassScaledMollifier {d : ℕ} (R : ℝ)
    (x y : Vec d) :
    gradient (fun z => Calculus.unitMassScaledMollifier d R (z - y)) x =
      gradient (Calculus.unitMassScaledMollifier d R) (x - y) := by
  funext j
  exact coordinateDerivative_translated_unitMassScaledMollifier R x y j

/-- Center averaging of the literal source weight has mass one.
Source: `paper/main.tex:926–938`. -/
theorem integral_translated_unitMassScaledMollifier {d : ℕ} {R : ℝ}
    (hR : 0 < R) (x : Vec d) :
    (∫ y, Calculus.unitMassScaledMollifier d R (x - y)) = 1 := by
  calc
    _ = ∫ y, Calculus.unitMassScaledMollifier d R (x + y) := by
      simpa only [sub_eq_add_neg] using
        integral_neg_eq_self (fun y => Calculus.unitMassScaledMollifier d R (x + y)) volume
    _ = ∫ y, Calculus.unitMassScaledMollifier d R y := integral_add_left_eq_self _ x
    _ = 1 := integral_unitMassScaledMollifier' hR

/-- The center-space kernel is integrable on any spatial set of finite
volume. This discharges the unweighted kernel premise in the local flux
assembly. Source: `paper/main.tex:926–938`. -/
theorem integrable_translated_unitMassScaledMollifier_product {d : ℕ} {R : ℝ}
    (hR : 0 < R) (U : Set (Vec d)) [IsFiniteMeasure (volume.restrict U)] :
    Integrable (fun z : Vec d × Vec d =>
      Calculus.unitMassScaledMollifier d R (z.2 - z.1))
      (volume.prod (volume.restrict U)) := by
  have hc := (contDiff_unitMassScaledMollifier (d := d) R).continuous
  have hm : Measurable (fun z : Vec d × Vec d =>
      Calculus.unitMassScaledMollifier d R (z.2 - z.1)) :=
    hc.measurable.comp (measurable_snd.sub measurable_fst)
  rw [integrable_prod_iff' hm.aestronglyMeasurable]
  refine ⟨Filter.Eventually.of_forall fun x => ?_, ?_⟩
  · exact (hc.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      ((hasCompactSupport_unitMassScaledMollifier hR).comp_homeomorph (Homeomorph.subLeft x))
  · have hnorm (x : Vec d) :
        (∫ y, ‖Calculus.unitMassScaledMollifier d R (x - y)‖) = 1 := by
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (unitMassScaledMollifier_nonneg' hR _)]
      exact integral_translated_unitMassScaledMollifier hR x
    simpa only [hnorm] using (integrable_const (1 : ℝ) :
      Integrable (fun _ : Vec d => (1 : ℝ)) (volume.restrict U))

end EinsteinRelation.Correctors
