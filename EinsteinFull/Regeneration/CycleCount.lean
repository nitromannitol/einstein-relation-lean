import Mathlib.Probability.StrongLaw

/-!
# Counting completed cycles

An increasing cycle clock defines the number of completed cycles as the last index whose
clock time is at most the observation time. This supplies the clock bracket used in the
renewal law for Gantert–Mathieu–Piatnitski, Proposition 5.9.
-/

open Filter
open scoped Topology

namespace EinsteinFull.Regeneration

/-- The number of completed cycles for a clock tending to infinity. -/
noncomputable def cycleCount (clock : ℕ → ℝ) (htop : Tendsto clock atTop atTop) (t : ℝ) : ℕ :=
  Nat.find ((htop.eventually_gt_atTop t).exists) - 1

/-- At nonnegative times, the cycle count is bracketed by its clock times. -/
theorem cycleCount_bracket (clock : ℕ → ℝ) (htop : Tendsto clock atTop atTop)
    (hzero : clock 0 = 0) (t : ℝ) (ht : 0 ≤ t) :
    clock (cycleCount clock htop t) ≤ t ∧ t < clock (cycleCount clock htop t + 1) := by
  let hex : ∃ n, t < clock n := (htop.eventually_gt_atTop t).exists
  have hpos : 0 < Nat.find hex := by
    by_contra hn
    have hzero' : Nat.find hex = 0 := Nat.eq_zero_of_not_pos hn
    have h := Nat.find_spec hex
    rw [hzero', hzero] at h
    exact (not_lt_of_ge ht) h
  have hsucc : Nat.find hex - 1 + 1 = Nat.find hex := Nat.sub_add_cancel hpos
  constructor
  · change clock (Nat.find hex - 1) ≤ t
    apply le_of_not_gt
    exact Nat.find_min hex (by omega)
  · change t < clock (Nat.find hex - 1 + 1)
    rw [hsucc]
    exact Nat.find_spec hex

/-- The count of completed cycles tends to infinity with time. -/
theorem cycleCount_tendsto_atTop (clock : ℕ → ℝ) (htop : Tendsto clock atTop atTop)
    (hzero : clock 0 = 0) (hmono : Monotone clock) :
    Tendsto (cycleCount clock htop) atTop atTop := by
  apply tendsto_atTop.2
  intro n
  filter_upwards [eventually_ge_atTop (clock n), eventually_ge_atTop (0 : ℝ)] with t hn ht
  have hb := (cycleCount_bracket clock htop hzero t ht).2
  by_contra h
  have hle : cycleCount clock htop t + 1 ≤ n := by omega
  have hclock := hmono hle
  linarith

end EinsteinFull.Regeneration
