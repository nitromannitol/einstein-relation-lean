import EinsteinFull.Regeneration.SplitContinuousKernel
import EinsteinFull.Regeneration.TrajectoryShift

/-!
# Deterministic grid shifts commute with compatible gluing

These are pathwise identities for the actual clamped-increment gluing. The
whole coin sequence shifts by the same number of grid intervals.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration

/-- Shifting compatible absolute-position segments commutes with gluing. -/
theorem glueSplitSegments_shift {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (γ : ℕ → Path d) (hcompat : ∀ n, γ (n + 1) 0 = γ n Δ) (n : ℕ) (t : ℝ≥0) :
    glueSplitSegments Δ hΔ γ (n * Δ + t) =
      glueSplitSegments Δ hΔ (sequenceShift n γ) t := by
  let k : ℕ := ⌊t / Δ⌋₊
  have hlow : k * Δ ≤ t := (le_div_iff₀ hΔ).mp (Nat.floor_le zero_le)
  have hhigh : t ≤ (k + 1 : ℕ) * Δ := by
    have h := (div_lt_iff₀ hΔ).mp (Nat.lt_floor_add_one (t / Δ))
    exact le_of_lt (by simpa only [Nat.cast_add, Nat.cast_one] using h)
  have hu : t - k * Δ ≤ Δ := by
    apply tsub_le_iff_right.mpr
    simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using hhigh
  have ht : t = k * Δ + (t - k * Δ) := (add_tsub_cancel_of_le hlow).symm
  have hcompat' : ∀ j, sequenceShift n γ (j + 1) 0 = sequenceShift n γ j Δ := by
    intro j
    simpa only [sequenceShift, Nat.add_assoc] using hcompat (n + j)
  calc
    glueSplitSegments Δ hΔ γ (n * Δ + t) =
        glueSplitSegments Δ hΔ γ ((n + k : ℕ) * Δ + (t - k * Δ)) := by
      congr 1
      calc
        n * Δ + t = n * Δ + (k * Δ + (t - k * Δ)) := congrArg _ ht
        _ = _ := by push_cast; ring
    _ = γ (n + k) (t - k * Δ) := glueSplitSegments_interval Δ hΔ γ hcompat _ _ hu
    _ = glueSplitSegments Δ hΔ (sequenceShift n γ) (k * Δ + (t - k * Δ)) :=
      (glueSplitSegments_interval Δ hΔ (sequenceShift n γ) hcompat' _ _ hu).symm
    _ = glueSplitSegments Δ hΔ (sequenceShift n γ) t := congrArg _ ht.symm

/-- The literal coupled grid shift equals gluing the shifted path/coin sequence. -/
theorem sampleTimeShift_gluedSplitSegmentSample {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (s : ℕ → SplitSegmentState d)
    (hcompat : ∀ n, (s (n + 1)).2.1 0 = (s n).2.1 Δ) (n : ℕ) :
    sampleTimeShift Δ (gluedSplitSegmentSample Δ hΔ s) (n * Δ) =
      gluedSplitSegmentSample Δ hΔ (sequenceShift n s) := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    exact glueSplitSegments_shift Δ hΔ (fun k => (s k).2.1) hcompat n t
  · funext k
    change (s (gridIndex Δ (n * Δ) + k)).2.2 = (s (n + k)).2.2
    rw [gridIndex_mul Δ hΔ n]

end EinsteinFull.Regeneration
