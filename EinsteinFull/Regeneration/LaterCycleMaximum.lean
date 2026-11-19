import EinsteinFull.Regeneration.LaterCycleVelocity

/-!
# The incomplete later cycle

The path displacement remaining after the last completed regeneration cycle is bounded by
the maximum displacement within that cycle. This supplies the pathwise remainder estimate
in the renewal argument of Gantert–Mathieu–Piatnitski, Proposition 5.9.
-/

open MeasureTheory Filter Finset EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- The largest absolute force-coordinate displacement from the start of a later cycle. -/
noncomputable def laterCycleMaximum {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (k : ℕ) (ωz : FieldPair d × CoupledSample d) : ℝ :=
  sSup ((fun s : ℝ≥0 => |ωz.2.1 ((regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal + s) i -
      ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal i|) ''
    Set.Icc 0 ((regenerationTime Δ lam R ωz.2 i (k + 2)).toNNReal -
      (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal))

/-- The sum of later-cycle rewards is the displacement between the first regeneration
and the endpoint of the last completed later cycle. -/
theorem sum_laterReward {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (ωz : FieldPair d × CoupledSample d) (k : ℕ) :
    (∑ j ∈ range k, laterReward Δ lam R i j ωz) =
      ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal i -
        ωz.2.1 (regenerationTime Δ lam R ωz.2 i 1).toNNReal i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    simp only [laterReward]
    ring

/-- A displacement within an interval is bounded by the maximum displacement from its start. -/
theorem displacement_le_interval_maximum {d : ℕ} (γ : Path d) (i : Fin d)
    (a b u : ℝ≥0) (ha : a ≤ u) (hb : u ≤ b) :
    |γ u i - γ a i| ≤ sSup ((fun s : ℝ≥0 => |γ (a + s) i - γ a i|) '' Set.Icc 0 (b - a)) := by
  have hf : Continuous (fun s : ℝ≥0 => |γ (a + s) i - γ a i|) := by fun_prop
  have hc : IsCompact ((fun s : ℝ≥0 => |γ (a + s) i - γ a i|) '' Set.Icc 0 (b - a)) :=
    isCompact_Icc.image hf
  apply le_csSup hc.bddAbove
  refine ⟨u - a, ⟨zero_le, tsub_le_tsub_right hb a⟩, ?_⟩
  change |γ (a + (u - a)) i - γ a i| = |γ u i - γ a i|
  rw [add_tsub_cancel_of_le ha]

/-- The literal incomplete-cycle remainder is bounded by the maximum of the current later
cycle when all regeneration times are finite. -/
theorem later_regeneration_remainder_le_maximum {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (ωz : FieldPair d × CoupledSample d)
    (hfinite : ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤) (t : ℝ) (ht : 0 ≤ t) :
    |laterPosition Δ lam R i ωz t -
      ∑ j ∈ range (laterCount Δ hΔ lam R i ωz t), laterReward Δ lam R i j ωz| ≤
        laterCycleMaximum Δ lam R i (laterCount Δ hΔ lam R i ωz t) ωz := by
  let k := laterCount Δ hΔ lam R i ωz t
  have heq : k = laterRegenerationCount Δ hΔ lam R ωz.2 i hfinite t := by
    simp only [k, laterCount, dite_eq_left hfinite]
  have hbracket := laterRegenerationCount_bracket Δ hΔ lam R ωz.2 i hfinite t ht
  rw [← heq, sum_laterCycleDuration, sum_laterCycleDuration] at hbracket
  have hlow : (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal ≤
      (regenerationTime Δ lam R ωz.2 i 1).toNNReal + t.toNNReal := by
    apply NNReal.coe_le_coe.mp
    have := hbracket.1
    dsimp [delayedRegenerationClock, regenerationClock] at this
    rw [NNReal.coe_add, Real.coe_toNNReal _ ht]
    simp only [ENNReal.coe_toNNReal_eq_toReal]
    linarith
  have hupp : (regenerationTime Δ lam R ωz.2 i 1).toNNReal + t.toNNReal ≤
      (regenerationTime Δ lam R ωz.2 i (k + 2)).toNNReal := by
    apply NNReal.coe_le_coe.mp
    have := hbracket.2.le
    dsimp [delayedRegenerationClock, regenerationClock] at this
    rw [NNReal.coe_add, Real.coe_toNNReal _ ht]
    simp only [ENNReal.coe_toNNReal_eq_toReal]
    linarith
  have hmax := displacement_le_interval_maximum ωz.2.1 i
    (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal
    (regenerationTime Δ lam R ωz.2 i (k + 2)).toNNReal
    ((regenerationTime Δ lam R ωz.2 i 1).toNNReal + t.toNNReal) hlow hupp
  change |laterPosition Δ lam R i ωz t - ∑ j ∈ range k, laterReward Δ lam R i j ωz| ≤
    laterCycleMaximum Δ lam R i k ωz
  rw [sum_laterReward]
  dsimp only [laterPosition, laterCycleMaximum]
  convert hmax using 1; congr 1; ring

end EinsteinFull.Regeneration
