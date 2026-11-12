import EinsteinRelation.Correctors.MollifierShiftSourceIdentity
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-! # Physical dilation of the literal mollifier

Source: `paper/main.tex:789–810,948–955`. These change-of-variable identities
retain the spatial Jacobian, the potential's amplitude, and the shift. They
hold for the Bochner integral without extra integrability assumptions.
-/

open MeasureTheory
open scoped Convolution

namespace EinsteinRelation.Correctors

/-- Dilation of the actual unit-mass mollifier, including its Jacobian.
Source: `paper/main.tex:789–810,948–955`. -/
theorem unitMassScaledMollifier_dilation {d : ℕ} {r R : ℝ}
    (hr : r ≠ 0) (hR : R ≠ 0) (x : Vec d) :
    Calculus.unitMassScaledMollifier d R (r • x) =
      (r ^ d)⁻¹ * Calculus.unitMassScaledMollifier d (R / r) x := by
  unfold Calculus.unitMassScaledMollifier
  rw [smul_smul, div_pow, inv_div, inv_div]
  have harg : R⁻¹ * r = r / R := by ring
  rw [harg]
  have hpow : r ^ d ≠ 0 := pow_ne_zero _ hr
  have hRpow : R ^ d ≠ 0 := pow_ne_zero _ hR
  field_simp

/-- Simultaneous transport of scale, shift and scalar amplitude in convolution.
Source: `paper/main.tex:789–810,948–955`. -/
theorem convolution_mollifier_dilation {d : ℕ} (f : Vec d → ℝ)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (c : ℝ) (y : Vec d) :
    ((fun x => c * f (r⁻¹ • x)) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      Calculus.unitMassScaledMollifier d R) y =
      c * (f ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        Calculus.unitMassScaledMollifier d (R / r)) (r⁻¹ • y) := by
  have hchange := Measure.integral_comp_smul_of_nonneg volume
    (fun x => c * f (r⁻¹ • x) * Calculus.unitMassScaledMollifier d R (y - x))
    r (hR := hr.le)
  have harg (x : Vec d) : y - r • x = r • (r⁻¹ • y - x) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  simp only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul] at hchange
  have heq : (fun x => c * f (r⁻¹ • (r • x)) *
      Calculus.unitMassScaledMollifier d R (y - r • x)) =
      (fun x => ((r ^ d)⁻¹ * c) *
        (f x * Calculus.unitMassScaledMollifier d (R / r) (r⁻¹ • y - x))) := by
    funext x
    rw [harg, unitMassScaledMollifier_dilation hr.ne' hR.ne',
      smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    ring
  rw [heq, integral_const_mul] at hchange
  simp only [convolution_def, ContinuousLinearMap.lsmul_apply, smul_eq_mul]
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero d hr.ne'))
  simpa only [mul_assoc] using hchange.symm

/-- The literal shifted-mean integral has the same dilation law, including
its potential amplitude. Source: `paper/main.tex:948–955`. -/
theorem mollifier_shift_integral_dilation {d : ℕ} (f : Vec d → ℝ)
    {r R : ℝ} (hr : 0 < r) (hR : 0 < R) (c : ℝ) (y : Vec d) :
    (∫ z, (Calculus.unitMassScaledMollifier d R z -
      Calculus.unitMassScaledMollifier d R (z - y)) * (c * f (r⁻¹ • z))) =
      c * ∫ z, (Calculus.unitMassScaledMollifier d (R / r) z -
        Calculus.unitMassScaledMollifier d (R / r) (z - r⁻¹ • y)) * f z := by
  have hchange := Measure.integral_comp_smul_of_nonneg volume
    (fun z => (Calculus.unitMassScaledMollifier d R z -
      Calculus.unitMassScaledMollifier d R (z - y)) * (c * f (r⁻¹ • z)))
    r (hR := hr.le)
  have harg (z : Vec d) : r • z - y = r • (z - r⁻¹ • y) := by
    rw [smul_sub, smul_smul, mul_inv_cancel₀ hr.ne', one_smul]
  simp only [Module.finrank_pi, Fintype.card_fin, smul_eq_mul] at hchange
  have heq : (fun z => (Calculus.unitMassScaledMollifier d R (r • z) -
      Calculus.unitMassScaledMollifier d R (r • z - y)) * (c * f (r⁻¹ • (r • z)))) =
      (fun z => ((r ^ d)⁻¹ * c) *
        ((Calculus.unitMassScaledMollifier d (R / r) z -
          Calculus.unitMassScaledMollifier d (R / r) (z - r⁻¹ • y)) * f z)) := by
    funext z
    rw [harg, unitMassScaledMollifier_dilation hr.ne' hR.ne',
      unitMassScaledMollifier_dilation hr.ne' hR.ne',
      smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    ring
  rw [heq, integral_const_mul] at hchange
  apply mul_left_cancel₀ (inv_ne_zero (pow_ne_zero d hr.ne'))
  simpa only [mul_assoc] using hchange.symm

end EinsteinRelation.Correctors
