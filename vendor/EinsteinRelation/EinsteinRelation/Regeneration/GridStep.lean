import EinsteinRelation.Regeneration.Rounding

open EinsteinRelation MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

/-!
Grid-step lower bounds for the infinity-preserving grid rounding `⌈t⌉_Δ` of `paper/main.tex:283`,
the prerequisite for the lower bound `τ_k ≥ 2kΔ` in `paper/main.tex:283–322`.

At a positive extended time, the rounding is at least one grid step `Δ`. For `t = ∞` the guard
returns `∞ ≥ Δ`. For finite `t > 0`, `t.toReal > 0`, so the real quotient `t.toReal / Δ` is
positive, `Nat.ceil` of a positive real is at least `1`, and multiplying `Δ` by a natural number
at least `1` gives a value at least `Δ`.

The equivalence `⌈t⌉_Δ = ∞ ↔ t = ∞` holds for every spacing `Δ`, including `Δ = 0`: a finite
input always produces a finite output because `Nat.ceil` returns a natural number.
-/

/-- At a positive extended time, the infinity-preserving grid rounding is at least one grid step
(`paper/main.tex:283`). -/
theorem extended_grid_rounding_ge_step (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (t : ℝ≥0∞) (ht : 0 < t) :
    (Δ : ℝ≥0∞) ≤ (if t = ⊤ then ⊤ else
      (((Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) := by
  by_cases ht_top : t = ⊤
  · rw [if_pos ht_top]
    exact le_top
  · rw [if_neg ht_top]
    have hΔR : (0 : ℝ) < (Δ : ℝ) := NNReal.coe_pos.mpr hΔ
    have htR : 0 < t.toReal := ENNReal.toReal_pos ht.ne' ht_top
    have hq : 0 < t.toReal / (Δ : ℝ) := div_pos htR hΔR
    have hk : 0 < Nat.ceil (t.toReal / (Δ : ℝ)) := Nat.ceil_pos.mpr hq
    have hk1 : (1 : ℝ≥0) ≤ ((Nat.ceil (t.toReal / (Δ : ℝ)) : ℕ) : ℝ≥0) :=
      Nat.one_le_cast.mpr (Nat.succ_le_of_lt hk)
    have hmul : Δ ≤ ((Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ≥0) * Δ : ℝ≥0) :=
      le_mul_of_one_le_left zero_le hk1
    exact ENNReal.coe_le_coe.mpr hmul

/-- The infinity-preserving grid rounding is infinite exactly at infinite times, for every spacing
(`paper/main.tex:283`). -/
theorem extended_grid_rounding_eq_top_iff (Δ : ℝ≥0) (t : ℝ≥0∞) :
    (if t = ⊤ then ⊤ else
      (((Nat.ceil (t.toReal / (Δ : ℝ)) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) = ⊤ ↔ t = ⊤ := by
  constructor
  · intro h
    by_contra ht_top
    rw [if_neg ht_top] at h
    exact ENNReal.coe_ne_top h
  · intro h
    rw [if_pos h]

end EinsteinRelation.Regeneration
