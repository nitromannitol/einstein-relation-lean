import EinsteinFull.Regeneration.SplitSegmentSequence
import EinsteinRelation.Diffusion.TimeChangeCovariance
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Algebra.Order.Floor.Semiring

/-!
# Measurable concatenation of compatible continuous segments

Sum the clamped increments of the actual segments. Their supports are locally
finite in time, so the sum defines a continuous path for every input sequence.
For compatible segments the sum telescopes, giving exactly the absolute
segment positions on every closed grid interval. The compact-open measurable
path API is reused from the blueprint's TimeChangeCovariance module.
-/

open MeasureTheory ProbabilityTheory Preorder Filter Topology
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration

/-- The increment of segment `n`, clamped to its own time interval. -/
def splitSegmentIncrement {d : ℕ} (Δ : ℝ≥0) (γ : ℕ → Path d) (n : ℕ) (t : ℝ≥0) : Vec d :=
  γ n (min Δ (t - n * Δ)) - γ n 0

theorem splitSegmentIncrement_eq_zero {d : ℕ} (Δ : ℝ≥0) (γ : ℕ → Path d)
    (n : ℕ) {t : ℝ≥0} (ht : t ≤ n * Δ) : splitSegmentIncrement Δ γ n t = 0 := by
  simp only [splitSegmentIncrement, tsub_eq_zero_of_le ht, min_eq_right (zero_le (a := Δ)), sub_self]

theorem continuous_splitSegmentIncrement {d : ℕ} (Δ : ℝ≥0) (γ : ℕ → Path d) (n : ℕ) :
    Continuous (splitSegmentIncrement Δ γ n) := by
  unfold splitSegmentIncrement
  exact ((γ n).continuous.comp (continuous_const.min (continuous_id.sub continuous_const))).sub
    continuous_const

private theorem locallyFinite_gridTails (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    LocallyFinite (fun n : ℕ => Set.Ioi (n * Δ)) := by
  intro t
  refine ⟨Set.Iio (t + Δ), Iio_mem_nhds (lt_add_of_pos_right t hΔ), ?_⟩
  apply (Set.finite_Iio (⌈(t + Δ) / Δ⌉₊ : ℕ)).subset
  rintro n ⟨u, hnu, hut⟩
  apply Nat.lt_ceil.mpr
  exact (lt_div_iff₀ hΔ).mpr (hnu.trans hut)

/-- Clamped increments have locally finite support in time. -/
theorem locallyFinite_splitSegmentIncrement {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (γ : ℕ → Path d) :
    LocallyFinite (fun n => Function.support (splitSegmentIncrement Δ γ n)) := by
  apply (locallyFinite_gridTails Δ hΔ).subset
  intro n t ht
  by_contra hn
  exact ht (splitSegmentIncrement_eq_zero Δ γ n (le_of_not_gt hn))

/-- Concatenate the clamped increments into a continuous path. On compatible
segments this agrees with each absolute-position segment on its entire closed
time interval. The definition itself needs no exceptional-set fallback. -/
def glueSplitSegments {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (γ : ℕ → Path d) : Path d :=
  ⟨fun t => γ 0 0 + ∑ᶠ n, splitSegmentIncrement Δ γ n t,
    continuous_const.add (continuous_finsum
      (continuous_splitSegmentIncrement Δ γ) (locallyFinite_splitSegmentIncrement Δ hΔ γ))⟩

/-- At a bounded time only the finitely many preceding increments contribute. -/
theorem glueSplitSegments_eq_sum {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (γ : ℕ → Path d) (N : ℕ) (t : ℝ≥0) (ht : t ≤ N * Δ) :
    glueSplitSegments Δ hΔ γ t =
      γ 0 0 + ∑ n ∈ Finset.range N, splitSegmentIncrement Δ γ n t := by
  classical
  change γ 0 0 + ∑ᶠ n, splitSegmentIncrement Δ γ n t = _
  congr 1
  apply finsum_eq_sum_of_support_subset
  intro n hn
  apply Finset.mem_range.mpr
  by_contra hN
  have hNn : (N : ℝ≥0) ≤ n := Nat.cast_le.mpr (Nat.le_of_not_gt hN)
  exact hn (splitSegmentIncrement_eq_zero Δ γ n
    (ht.trans (mul_le_mul_of_nonneg_right hNn Δ.2)))

/-- The actual gluing map is measurable into continuous path space. -/
theorem measurable_glueSplitSegments {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) :
    Measurable (glueSplitSegments (d := d) Δ hΔ) := by
  apply TimeChangeCovariance.measurable_path_of_forall_eval
  intro t
  let N : ℕ := ⌈t / Δ⌉₊
  have ht : t ≤ N * Δ := (div_le_iff₀ hΔ).mp (Nat.le_ceil (t / Δ))
  have heq : (fun γ : ℕ → Path d => glueSplitSegments Δ hΔ γ t) =
      fun γ => γ 0 0 + ∑ n ∈ Finset.range N, splitSegmentIncrement Δ γ n t := by
    funext γ
    exact glueSplitSegments_eq_sum Δ hΔ γ N t ht
  rw [heq]
  apply Measurable.add
  · exact (continuous_eval_const 0).measurable.comp (measurable_pi_apply 0)
  · apply Finset.measurable_sum
    intro n _
    exact ((continuous_eval_const (min Δ (t - n * Δ))).measurable.comp
      (measurable_pi_apply n)).sub
      ((continuous_eval_const 0).measurable.comp (measurable_pi_apply n))

/-- For compatible segments, the sum of all completed increments is exactly
the starting position of the next segment. -/
theorem splitSegment_prefix_sum {d : ℕ} (Δ : ℝ≥0) (γ : ℕ → Path d)
    (hcompat : ∀ n, γ (n + 1) 0 = γ n Δ) (n : ℕ) :
    γ 0 0 + ∑ j ∈ Finset.range n, (γ j Δ - γ j 0) = γ n 0 := by
  induction n with
  | zero => simp only [Finset.range_zero, Finset.sum_empty, add_zero]
  | succ n hn =>
    rw [Finset.sum_range_succ, ← add_assoc, hn, hcompat n]
    abel

/-- Compatible absolute-position segments are reproduced on every closed
grid interval, including both endpoints. -/
theorem glueSplitSegments_interval {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (γ : ℕ → Path d) (hcompat : ∀ n, γ (n + 1) 0 = γ n Δ)
    (n : ℕ) (u : ℝ≥0) (hu : u ≤ Δ) :
    glueSplitSegments Δ hΔ γ (n * Δ + u) = γ n u := by
  classical
  have ht : n * Δ + u ≤ (n + 1 : ℕ) * Δ := by
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul] using add_le_add (le_refl (n * Δ)) hu
  rw [glueSplitSegments_eq_sum Δ hΔ γ (n + 1) _ ht, Finset.sum_range_succ]
  have hj : ∀ j ∈ Finset.range n,
      splitSegmentIncrement Δ γ j (n * Δ + u) = γ j Δ - γ j 0 := by
    intro j hj
    have hjn : (j + 1 : ℕ) ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
    have hΔj : Δ ≤ n * Δ + u - j * Δ := by
      apply le_tsub_of_add_le_right
      have hcast : ((j + 1 : ℕ) : ℝ≥0) ≤ n := Nat.cast_le.mpr hjn
      calc
        Δ + j * Δ = ((j + 1 : ℕ) : ℝ≥0) * Δ := by push_cast; ring
        _ ≤ n * Δ := mul_le_mul_of_nonneg_right hcast Δ.2
        _ ≤ n * Δ + u := le_add_of_nonneg_right u.2
    simp only [splitSegmentIncrement, min_eq_left hΔj]
  rw [Finset.sum_congr rfl hj, ← add_assoc, splitSegment_prefix_sum Δ γ hcompat]
  have hn : splitSegmentIncrement Δ γ n (n * Δ + u) = γ n u - γ n 0 := by
    simp only [splitSegmentIncrement, add_tsub_cancel_left, min_eq_right hu]
  rw [hn]
  abel

end EinsteinFull.Regeneration
