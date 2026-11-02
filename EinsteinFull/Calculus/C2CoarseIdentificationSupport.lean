import EinsteinFull.External.Draft.AKMCoarsenedCoefficientEstimates
import EinsteinRelation.Correctors.SpatialWeakProduct
import EinsteinRelation.TimeChange.EuclideanTransport

/-! Deterministic normalization inside the genuine source A₁ class.
These lemmas do not assert the covariance reduction. -/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinFull.External.Source.AKM EinsteinFull.External.Draft

/-- Scalar multiplication preserves all fields of the source harmonic class. -/
def smulSubquadraticHarmonic {d : ℕ} {K : ℝ} {a : Coefficient d K}
    (c : ℝ) (w : SubquadraticHarmonic a) : SubquadraticHarmonic a where
  potential := fun x => c * w.potential x
  grad := fun x => c • w.grad x
  weak_gradient := by
    simpa [coordinateDerivative, Pi.smul_apply, smul_eq_mul] using!
      EinsteinRelation.Correctors.hasWeakGradient_mul_smooth isOpen_univ w.weak_gradient
        (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec d => c))
  local_energy := by
    intro R hR
    refine ⟨(w.local_energy R hR).1.const_mul c, ?_⟩
    simpa only [TimeChange.euclideanNorm_smul] using
      (w.local_energy R hR).2.const_mul |c|
  harmonic := by
    have h := EinsteinRelation.Correctors.hasWeakDivergence_mul_smooth
      isOpen_univ w.harmonic
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec d => c))
    simpa [gradient, coordinateDerivative, dot, Matrix.mulVec_smul,
      Pi.smul_apply, smul_eq_mul] using! h
  growth := by
    have h := w.growth.const_mul |c|
    simp only [mul_zero] at h
    convert h using 1
    funext R
    simp only [abs_mul, mul_pow, sq_abs, average_const_mul,
      Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]
    ring

/-- The flux residual scales with the very same source function; no selected
localized energy or replacement harmonic representative enters. -/
theorem coarseFluxResidual_smul {d : ℕ} {K : ℝ} {a : Coefficient d K}
    (A : Mat d) (z : Vec d) (r c : ℝ) (w : SubquadraticHarmonic a) :
    ((∫ x, heatKernel z r x • (a x).mulVec ((smulSubquadraticHarmonic c w).grad x)) -
      (A + coarsenedCoefficient a A z r).mulVec
        (∫ x, heatKernel z r x • (smulSubquadraticHarmonic c w).grad x)) =
    c • ((∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) -
      (A + coarsenedCoefficient a A z r).mulVec
        (∫ x, heatKernel z r x • w.grad x)) := by
  simp only [smulSubquadraticHarmonic, Matrix.mulVec_smul, smul_comm (heatKernel z r _)
    c, integral_smul, smul_sub]

/-- The Gaussian normalization scales by the absolute value of the scalar.
The kernel is the isotropic source kernel throughout. -/
theorem coarseGradientSize_smul {d : ℕ} {K : ℝ} {a : Coefficient d K}
    (z : Vec d) (r c : ℝ) (w : SubquadraticHarmonic a) :
    Real.sqrt (∫ x, heatKernel z r x *
      euclideanNorm ((smulSubquadraticHarmonic c w).grad x) ^ 2) =
    |c| * Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (w.grad x) ^ 2) := by
  have hfun : (fun x => heatKernel z r x *
      euclideanNorm ((smulSubquadraticHarmonic c w).grad x) ^ 2) =
      (fun x => c ^ 2 * (heatKernel z r x * euclideanNorm (w.grad x) ^ 2)) := by
    funext x
    simp only [smulSubquadraticHarmonic, TimeChange.euclideanNorm_smul, mul_pow, sq_abs]
    ring
  rw [hfun, integral_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- Application of the source supremum to a normalized member of A₁.
Boundedness of the defining set is an explicit internal deterministic
obligation; the total real supremum alone cannot supply it. -/
theorem coarseFluxResidual_le_of_normalized {d : ℕ} {K : ℝ} {a : Coefficient d K}
    (A : Mat d) (z : Vec d) (r : ℝ) (w : SubquadraticHarmonic a)
    (hi : Integrable (fun x => heatKernel z r x * euclideanNorm (w.grad x) ^ 2))
    (hn : Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (w.grad x) ^ 2) ≤ 1)
    (hb : BddAbove {e : ℝ | ∃ v : SubquadraticHarmonic a,
      Integrable (fun x => heatKernel z r x * euclideanNorm (v.grad x) ^ 2) ∧
      Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (v.grad x) ^ 2) ≤ 1 ∧
      e = euclideanNorm
        ((∫ x, heatKernel z r x • (a x).mulVec (v.grad x)) -
          (A + coarsenedCoefficient a A z r).mulVec
            (∫ x, heatKernel z r x • v.grad x))}) :
    euclideanNorm
      ((∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) -
        (A + coarsenedCoefficient a A z r).mulVec
          (∫ x, heatKernel z r x • w.grad x)) ≤
      normalizedCoarseFluxDefect a A z r := by
  exact le_csSup hb ⟨w, hi, hn, rfl⟩

/-- Normalize a positive-energy source harmonic function, apply the actual
supremum, and restore its original Gaussian energy factor. -/
theorem coarseFluxResidual_le_gradientSize_mul {d : ℕ} {K : ℝ}
    {a : Coefficient d K} (A : Mat d) (z : Vec d) (r : ℝ)
    (w : SubquadraticHarmonic a)
    (hi : Integrable (fun x => heatKernel z r x * euclideanNorm (w.grad x) ^ 2))
    (hn : 0 < Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (w.grad x) ^ 2))
    (hb : BddAbove {e : ℝ | ∃ v : SubquadraticHarmonic a,
      Integrable (fun x => heatKernel z r x * euclideanNorm (v.grad x) ^ 2) ∧
      Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (v.grad x) ^ 2) ≤ 1 ∧
      e = euclideanNorm
        ((∫ x, heatKernel z r x • (a x).mulVec (v.grad x)) -
          (A + coarsenedCoefficient a A z r).mulVec
            (∫ x, heatKernel z r x • v.grad x))}) :
    euclideanNorm
      ((∫ x, heatKernel z r x • (a x).mulVec (w.grad x)) -
        (A + coarsenedCoefficient a A z r).mulVec
          (∫ x, heatKernel z r x • w.grad x)) ≤
      Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (w.grad x) ^ 2) *
        normalizedCoarseFluxDefect a A z r := by
  let N := Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (w.grad x) ^ 2)
  let v := smulSubquadraticHarmonic N⁻¹ w
  have hvi : Integrable (fun x => heatKernel z r x * euclideanNorm (v.grad x) ^ 2) := by
    apply (hi.const_mul (N⁻¹ ^ 2)).congr
    apply ae_of_all
    intro x
    simp only [v, smulSubquadraticHarmonic, TimeChange.euclideanNorm_smul,
      mul_pow, sq_abs]
    ring
  have hvn : Real.sqrt (∫ x, heatKernel z r x * euclideanNorm (v.grad x) ^ 2) ≤ 1 := by
    rw [coarseGradientSize_smul]
    exact le_of_eq (by rw [abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne'])
  have h := coarseFluxResidual_le_of_normalized A z r v hvi hvn hb
  rw [coarseFluxResidual_smul, TimeChange.euclideanNorm_smul,
    abs_of_pos (inv_pos.mpr hn)] at h
  have hm := mul_le_mul_of_nonneg_left h hn.le
  simpa only [← mul_assoc, mul_inv_cancel₀ hn.ne', one_mul] using hm

end EinsteinFull
