import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import EinsteinRelation.Calculus.HorizontalSobolev
import EinsteinRelation.Calculus.HorizontalTranslationLp

/-! # Full-H¹ translation-orbit weak derivative

For the actual horizontal H¹ subspace, integration by parts in the spatial translation variable
identifies the L²-valued weak derivative with the translated horizontal generator gradient.
The identity uses the source translation action and strong generator domain from
`paper/main.tex:237–245`; it does not assert a corrector characterization.
-/

open MeasureTheory

namespace EinsteinRelation

variable {d : ℕ}

private theorem translationLp_lineDeriv {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (i : Fin d)
    (f g : Lp ℝ 2 Q) (hfg : HasHorizontalLpDerivative Q hQ i f g)
    (x : Vec d) :
    HasLineDerivAt ℝ (fun y : Vec d => translationLp Q hQ y f)
      (translationLp Q hQ x g) x (unitVector i) := by
  have hzero : HasDerivAt
      (fun t : ℝ => translationLp Q hQ (t • unitVector i) f) g 0 := by
    have hslope : slope
        (fun t : ℝ => translationLp Q hQ (t • unitVector i) f) 0 =
          fun t => t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f) := by
      funext t
      simp only [slope_def_module, sub_zero]
      rw [zero_smul, translationLp_zero]
    rw [hasDerivAt_iff_tendsto_slope, hslope]
    exact hfg
  have hrec : HasDerivAt
      (fun t : ℝ => translationLp Q hQ (x + t • unitVector i) f)
      (translationLp Q hQ x g) 0 := by
    have hgroup : (fun t : ℝ => translationLp Q hQ (x + t • unitVector i) f) =
        (fun t => translationLp Q hQ x
          (translationLp Q hQ (t • unitVector i) f)) := by
      funext t
      exact translationLp_add Q hQ x (t • unitVector i) f
    rw [hgroup]
    exact (translationLp Q hQ x).toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt_of_eq
        0 hzero rfl
  simpa only [HasLineDerivAt] using hrec

/-- For every compact smooth spatial test, the full horizontal-H¹ generator derivative gives the
L²-valued distribution identity of the literal translation orbit. The integrals are Bochner
integrals in the environment L² space; no samplewise representative or test-dependent null set
is chosen. -/
theorem horizontalH1_orbit_hasLpWeakPartialDerivative {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : horizontalH1 Q hQ) (i : Fin d)
    {φ : Vec d → ℝ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    (∫ x : Vec d, coordinateDerivative i φ x •
      translationLp Q hQ x (f : Lp ℝ 2 Q)) =
      - ∫ x : Vec d, φ x • translationLp Q hQ x
        (horizontalH1Gradient Q hQ f i) := by
  let u : Vec d → Lp ℝ 2 Q := fun x => translationLp Q hQ x (f : Lp ℝ 2 Q)
  let v : Vec d → Lp ℝ 2 Q := fun x =>
    translationLp Q hQ x (horizontalH1Gradient Q hQ f i)
  have hu : Continuous u :=
    (continuous_translationLp Q hQ).comp
      (continuous_id.prodMk continuous_const)
  have hv : Continuous v :=
    (continuous_translationLp Q hQ).comp
      (continuous_id.prodMk continuous_const)
  have hφ' : Continuous (coordinateDerivative i φ) := by
    unfold coordinateDerivative
    exact (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ'c : HasCompactSupport (coordinateDerivative i φ) := by
    unfold coordinateDerivative
    exact HasCompactSupport.fderiv_apply (𝕜 := ℝ) hφc (unitVector i)
  have hφline : ∀ x : Vec d,
      HasLineDerivAt ℝ φ (coordinateDerivative i φ x) x (unitVector i) := by
    intro x
    unfold coordinateDerivative
    exact (hφ.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt (unitVector i)
  have huline : ∀ x : Vec d,
      HasLineDerivAt ℝ u (v x) x (unitVector i) := by
    intro x
    exact translationLp_lineDeriv hQ i (f : Lp ℝ 2 Q)
      (horizontalH1Gradient Q hQ f i)
      (hasHorizontalLpDerivative_horizontalH1Gradient Q hQ f i) x
  have hu_int : Integrable (fun x : Vec d => φ x • u x) := by
    exact (hφ.continuous.smul hu).integrable_of_hasCompactSupport hφc.smul_right
  have hvφ_int : Integrable (fun x : Vec d => φ x • v x) := by
    exact (hφ.continuous.smul hv).integrable_of_hasCompactSupport hφc.smul_right
  have huφ'_int : Integrable (fun x : Vec d => coordinateDerivative i φ x • u x) := by
    exact (hφ'.smul hu).integrable_of_hasCompactSupport hφ'c.smul_right
  have hparts := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (E := Vec d) (F := ℝ) (G := Lp ℝ 2 Q) (W := Lp ℝ 2 Q)
    (μ := volume) (B := ContinuousLinearMap.lsmul ℝ ℝ)
    huφ'_int hvφ_int hu_int (fun x _ => hφline x) (fun x _ => huline x)
  simpa only [neg_neg, ContinuousLinearMap.lsmul_apply] using
    (congrArg Neg.neg hparts).symm

end EinsteinRelation
