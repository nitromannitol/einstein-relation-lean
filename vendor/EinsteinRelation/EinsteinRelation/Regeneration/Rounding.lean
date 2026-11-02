import EinsteinRelation.Diffusion.Basic
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Set.Insert
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic

open EinsteinRelation MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

/-!
The infinity-preserving grid rounding `⌈t⌉_Δ` of `paper/main.tex:283`: the least multiple of
`Δ` that is at least `t`, with `⌈∞⌉_Δ = ∞`. For finite `t` the frozen expression below equals
`⌈t / Δ⌉₊ * Δ`, and the guard `t = ⊤` keeps infinity fixed.

Majorization uses `Nat.le_ceil` on the real quotient `t.toReal / Δ` and multiplies back by
`Δ > 0`. Measurability uses only measurability of `ENNReal.toReal`, division by a constant,
`Nat.ceil`, natural casts, multiplication by a constant, the coercion `ℝ≥0 → ℝ≥0∞`, and a
measurable `ite` on the singleton `{⊤}`. No positivity hypothesis enters that proof.
-/

/-- Every extended time is majorized by its infinity-preserving grid rounding
(`paper/main.tex:283`). -/
theorem le_extended_grid_rounding (Δ : ℝ≥0) (hΔ : 0 < Δ) (t : ℝ≥0∞) :
    t ≤ if t = ⊤ then ⊤ else
      (((Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
  by_cases ht : t = ⊤
  · rw [if_pos ht]
    exact le_top
  · rw [if_neg ht]
    have hΔR : (0 : ℝ) < (Δ : ℝ) := NNReal.coe_pos.mpr hΔ
    have hceil : t.toReal / (Δ : ℝ) ≤ (Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ) := Nat.le_ceil _
    have hreal : t.toReal ≤ (((Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ≥0) * Δ : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_mul, NNReal.coe_natCast]
      calc t.toReal = t.toReal / (Δ : ℝ) * (Δ : ℝ) := (div_mul_cancel₀ _ hΔR.ne').symm
        _ ≤ (Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ) * (Δ : ℝ) :=
          mul_le_mul_of_nonneg_right hceil hΔR.le
    calc t = ENNReal.ofReal t.toReal := (ENNReal.ofReal_toReal ht).symm
      _ ≤ ENNReal.ofReal (((Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ≥0) * Δ : ℝ≥0) : ℝ) :=
          ENNReal.ofReal_le_ofReal hreal
      _ = (((Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
          rw [ENNReal.ofReal_coe_nnreal]

/-- Measurability of the infinity-preserving grid rounding on `ℝ≥0∞`
(`paper/main.tex:283`). The statement carries no positivity hypothesis. -/
theorem measurable_extended_grid_rounding (Δ : ℝ≥0) :
    Measurable (fun t : ℝ≥0∞ => if t = ⊤ then ⊤ else
      (((Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) := by
  have hfloor : Measurable (fun t : ℝ≥0∞ => Nat.ceil (t.toReal / (Δ : ℝ))) :=
    (ENNReal.measurable_toReal.div_const (Δ : ℝ)).nat_ceil
  have hnat : Measurable (fun t : ℝ≥0∞ => ((Nat.ceil (t.toReal / (Δ : ℝ)) : ℕ) : ℝ≥0)) :=
    (measurable_from_nat (f := fun n : ℕ => (n : ℝ≥0))).comp hfloor
  have hcoe : Measurable (fun t : ℝ≥0∞ =>
      (((Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :=
    measurable_coe_nnreal_ennreal.comp (hnat.mul_const Δ)
  have hset : MeasurableSet {t : ℝ≥0∞ | t = ⊤} := by
    rw [Set.setOf_eq_eq_singleton]
    exact measurableSet_singleton ⊤
  exact Measurable.ite hset measurable_const hcoe

end EinsteinRelation.Regeneration
