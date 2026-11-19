import EinsteinFull.Regeneration.LaterCountLaw
import EinsteinFull.Regeneration.CoordinateVelocity

/-!
# Coordinate rewards of regeneration cycles

A regeneration construction is oriented along the force, while each coordinate has its own
cycle reward. The delayed renewal argument applies to every coordinate once the
corresponding cycle laws and maximum moments are available.
-/

open MeasureTheory Filter Finset ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology ProbabilityTheory Function

namespace EinsteinFull.Regeneration

/-- The displacement in coordinate `j` of a later cycle oriented along `i`. -/
noncomputable def laterCoordinateReward {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i j : Fin d)
    (k : ℕ) (ωz : FieldPair d × CoupledSample d) : ℝ :=
  ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 2)).toNNReal j -
    ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal j

/-- The displacement in coordinate `j` after the first regeneration oriented along `i`. -/
noncomputable def laterCoordinatePosition {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i j : Fin d)
    (ωz : FieldPair d × CoupledSample d) (t : ℝ) : ℝ :=
  ωz.2.1 ((regenerationTime Δ lam R ωz.2 i 1).toNNReal + t.toNNReal) j -
    ωz.2.1 (regenerationTime Δ lam R ωz.2 i 1).toNNReal j

/-- The maximum absolute displacement in coordinate `j` over a later cycle. -/
noncomputable def laterCoordinateMaximum {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i j : Fin d)
    (k : ℕ) (ωz : FieldPair d × CoupledSample d) : ℝ :=
  sSup ((fun s : ℝ≥0 => |ωz.2.1 ((regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal + s) j -
      ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal j|) ''
    Set.Icc 0 ((regenerationTime Δ lam R ωz.2 i (k + 2)).toNNReal -
      (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal))

/-- Later coordinate rewards telescope to the displacement at the last completed cycle. -/
theorem sum_laterCoordinateReward {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i j : Fin d)
    (ωz : FieldPair d × CoupledSample d) (k : ℕ) :
    (∑ a ∈ range k, laterCoordinateReward Δ lam R i j a ωz) =
      ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal j -
        ωz.2.1 (regenerationTime Δ lam R ωz.2 i 1).toNNReal j := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    simp only [laterCoordinateReward]
    ring

/-- The incomplete-cycle remainder in any coordinate is bounded by that cycle's maximum. -/
theorem later_coordinate_remainder_le_maximum {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i j : Fin d)
    (ωz : FieldPair d × CoupledSample d)
    (hfinite : ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤) (t : ℝ) (ht : 0 ≤ t) :
    |laterCoordinatePosition Δ lam R i j ωz t -
      ∑ a ∈ range (laterCount Δ hΔ lam R i ωz t), laterCoordinateReward Δ lam R i j a ωz| ≤
        laterCoordinateMaximum Δ lam R i j (laterCount Δ hΔ lam R i ωz t) ωz := by
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
  have hmax := displacement_le_interval_maximum ωz.2.1 j
    (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal
    (regenerationTime Δ lam R ωz.2 i (k + 2)).toNNReal
    ((regenerationTime Δ lam R ωz.2 i 1).toNNReal + t.toNNReal) hlow hupp
  change |laterCoordinatePosition Δ lam R i j ωz t -
    ∑ a ∈ range k, laterCoordinateReward Δ lam R i j a ωz| ≤ laterCoordinateMaximum Δ lam R i j k ωz
  rw [sum_laterCoordinateReward]
  dsimp only [laterCoordinatePosition, laterCoordinateMaximum]
  convert hmax using 1; congr 1; ring

/-- Under the later-cycle laws and an integrable independent coordinate maximum, the original
coupled path has the corresponding coordinate velocity. -/
theorem coupled_later_coordinate_velocity {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i j : Fin d)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤)
    (hr : Integrable (laterCoordinateReward Δ lam R i j 0) (annealedCoupledLaw Q K))
    (ht : Integrable (laterDuration Δ lam R i 0) (annealedCoupledLaw Q K))
    (hir : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterCoordinateReward Δ lam R i j))
    (hit : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterDuration Δ lam R i))
    (hdr : ∀ n, IdentDistrib (laterCoordinateReward Δ lam R i j n) (laterCoordinateReward Δ lam R i j 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hdt : ∀ n, IdentDistrib (laterDuration Δ lam R i n) (laterDuration Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hm : Integrable (laterCoordinateMaximum Δ lam R i j 0) (annealedCoupledLaw Q K))
    (him : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterCoordinateMaximum Δ lam R i j))
    (hdm : ∀ n, IdentDistrib (laterCoordinateMaximum Δ lam R i j n) (laterCoordinateMaximum Δ lam R i j 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K)) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto
      (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ωz.2.1 t j) atTop
      (𝓝 ((∫ ωz, laterCoordinateReward Δ lam R i j 0 ωz ∂annealedCoupledLaw Q K) /
        ∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K)) := by
  have hmean := laterDuration_integral_pos Q K hK Δ hΔ lam R i hfinite ht
  have hcount := laterCount_tendsto_ae Q K Δ hΔ lam R i hfinite
  have hbracket := laterCount_bracket_ae Q K Δ hΔ lam R i hfinite
  have hrate : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      Tendsto (fun t : ℝ => (laterCount Δ hΔ lam R i ωz t : ℝ) / t) atTop
        (𝓝 (∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K)⁻¹) := by
    filter_upwards [strong_law_ae (laterDuration Δ lam R i) ht hit hdt, hcount, hbracket]
      with ωz hs hc hb
    have hclock : Tendsto (fun n : ℕ => (∑ a ∈ range n, laterDuration Δ lam R i a ωz) / (n : ℝ))
        atTop (𝓝 (∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K)) := by
      simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hs
    exact cycle_count_rate_of_clock (fun n => ∑ a ∈ range n, laterDuration Δ lam R i a ωz)
      (laterCount Δ hΔ lam R i ωz) _ hmean hclock hc hb
  have hbound : ∀ᵐ ωz ∂annealedCoupledLaw Q K, ∀ᶠ t in atTop,
      |laterCoordinatePosition Δ lam R i j ωz t -
        ∑ a ∈ range (laterCount Δ hΔ lam R i ωz t), laterCoordinateReward Δ lam R i j a ωz| ≤
          laterCoordinateMaximum Δ lam R i j (laterCount Δ hΔ lam R i ωz t) ωz := by
    filter_upwards [hfinite] with ωz hf
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht0
    exact later_coordinate_remainder_le_maximum Δ hΔ lam R i j ωz hf t ht0
  have hrem := remainder_div_time_tendsto_zero_ae (annealedCoupledLaw Q K)
    (laterCoordinateMaximum Δ lam R i j) (laterCount Δ hΔ lam R i)
    (fun ωz t => laterCoordinatePosition Δ lam R i j ωz t -
      ∑ a ∈ range (laterCount Δ hΔ lam R i ωz t), laterCoordinateReward Δ lam R i j a ωz)
    _ hm him hdm hcount hrate hbound
  have hv := reward_rate_of_cycle_clock_ae (annealedCoupledLaw Q K) (laterCoordinateReward Δ lam R i j)
    (laterDuration Δ lam R i) (laterCount Δ hΔ lam R i) (laterCoordinatePosition Δ lam R i j)
    hr ht hir hit hdr hdt hmean hcount hbracket hrem
  filter_upwards [hv] with ωz hωz
  exact coordinate_velocity_of_time_shift ωz.2.1 j (regenerationTime Δ lam R ωz.2 i 1).toNNReal _ hωz

end EinsteinFull.Regeneration
