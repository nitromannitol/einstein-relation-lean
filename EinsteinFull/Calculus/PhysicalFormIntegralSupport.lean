import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Analysis.Complex.Basic

open scoped ENNReal
open MeasureTheory
namespace EinsteinFull

/-- Bounded coefficient fields pair two square-integrable shifted gradients. -/
theorem integrable_shiftedGradientForm {X : Type*} [MeasurableSpace X]
    (m : Measure X) (d : ℕ) (a : Fin d → Fin d → X → ℂ) (B : ℝ)
    (ha : ∀ j k, AEStronglyMeasurable (a j k) m)
    (hab : ∀ j k, ∀ᵐ x ∂m, ‖a j k x‖ ≤ B)
    (u v : X → ℂ) (G H : Fin d → X → ℂ)
    (hu : MemLp u 2 m) (hv : MemLp v 2 m)
    (hG : ∀ j, MemLp (G j) 2 m) (hH : ∀ j, MemLp (H j) 2 m)
    (b : Fin d → ℂ) :
    Integrable (fun x => ∑ j : Fin d, ∑ k : Fin d,
      (G j x - b j * u x) * a j k x * (H k x - b k * v x)) m := by
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  have hf : MemLp (fun x => G j x - b j * u x) 2 m := (hG j).sub (hu.const_mul _)
  have hg : MemLp (fun x => H k x - b k * v x) 2 m := (hH k).sub (hv.const_mul _)
  have hprod := (hf.integrable_mul hg).bdd_mul (ha j k) (hab j k)
  convert hprod using 1
  ext x
  dsimp
  ring


/-- L infinity coefficients suffice without a chosen pointwise bound. -/
theorem integrable_shiftedGradientForm_of_memLp {X : Type*} [MeasurableSpace X]
    (m : Measure X) (d : ℕ) (a : Fin d → Fin d → X → ℂ)
    (ha : ∀ j k, MemLp (a j k) ∞ m)
    (u v : X → ℂ) (G H : Fin d → X → ℂ)
    (hu : MemLp u 2 m) (hv : MemLp v 2 m)
    (hG : ∀ j, MemLp (G j) 2 m) (hH : ∀ j, MemLp (H j) 2 m)
    (b : Fin d → ℂ) :
    Integrable (fun x => ∑ j : Fin d, ∑ k : Fin d,
      (G j x - b j * u x) * a j k x * (H k x - b k * v x)) m := by
  apply integrable_finsetSum
  intro j _
  apply integrable_finsetSum
  intro k _
  have hf : MemLp (fun x => G j x - b j * u x) 2 m := (hG j).sub (hu.const_mul _)
  have hg : MemLp (fun x => H k x - b k * v x) 2 m := (hH k).sub (hv.const_mul _)
  have hprod := (hf.integrable_mul hg).mul_of_top_right (ha j k)
  convert hprod using 1
  ext x
  dsimp
  ring

end EinsteinFull
