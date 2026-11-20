import Mathlib.Analysis.MeanInequalitiesPow
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Function.L2Space

/-! # Finite square integrals of sums

The sum of two nonnegative extended-real random variables has a finite square integral when
both terms do.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}

/-- Finite square integrals are stable under addition. -/
theorem lintegral_add_sq_lt_top (f g : Ω → ℝ≥0∞) (hf : Measurable f)
    (hf2 : (∫⁻ ω, f ω ^ 2 ∂P) < ⊤) (hg2 : (∫⁻ ω, g ω ^ 2 ∂P) < ⊤) :
    (∫⁻ ω, (f ω + g ω) ^ 2 ∂P) < ⊤ := by
  have hpoint (ω : Ω) : (f ω + g ω) ^ 2 ≤ 2 * (f ω ^ 2 + g ω ^ 2) := by
    have h := ENNReal.rpow_add_le_mul_rpow_add_rpow (f ω) (g ω) (p := 2) (by norm_num)
    simpa only [ENNReal.rpow_two, show (2 : ℝ) - 1 = 1 by norm_num, ENNReal.rpow_one] using h
  calc
    (∫⁻ ω, (f ω + g ω) ^ 2 ∂P) ≤ ∫⁻ ω, 2 * (f ω ^ 2 + g ω ^ 2) ∂P :=
      lintegral_mono hpoint
    _ = 2 * ((∫⁻ ω, f ω ^ 2 ∂P) + ∫⁻ ω, g ω ^ 2 ∂P) := by
      rw [lintegral_const_mul' _ _ (by norm_num), lintegral_add_left (hf.pow_const 2)]
    _ < ⊤ := ENNReal.mul_lt_top (by norm_num) (ENNReal.add_lt_top.mpr ⟨hf2, hg2⟩)

/-- A square-integrable real variable has a finite extended-real square integral. -/
theorem lintegral_ofReal_abs_sq_lt_top (f : Ω → ℝ) (hf : MemLp f 2 P) :
    (∫⁻ ω, ENNReal.ofReal |f ω| ^ 2 ∂P) < ⊤ := by
  have h := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top
    (p := (2 : ℝ≥0∞)) (f := f) (μ := P) (by norm_num) (by norm_num) hf
  simpa only [ENNReal.toReal_ofNat, ← ofReal_norm, Real.norm_eq_abs, ENNReal.rpow_two] using h

end EinsteinFull.External.DFGW
