import EinsteinFull.Regeneration.LaterCountLaw

/-!
# Rates of increasing profiles along regeneration cycles

An increasing profile is bracketed by its values at successive regeneration times. Its
cycle increments therefore yield an asymptotic rate without a separate remainder bound.
-/

open MeasureTheory Filter Finset ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology ProbabilityTheory Function

namespace EinsteinFull.Regeneration

/-- Later-cycle increments of an environment-and-path dependent profile. -/
noncomputable def laterProfileReward {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (F : (FieldPair d × CoupledSample d) → ℝ≥0 → ℝ) (k : ℕ)
    (ωz : FieldPair d × CoupledSample d) : ℝ :=
  F ωz (regenerationTime Δ lam R ωz.2 i (k + 2)).toNNReal -
    F ωz (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal

/-- The profile increment since the first regeneration, at a given elapsed time. -/
noncomputable def laterProfilePosition {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (F : (FieldPair d × CoupledSample d) → ℝ≥0 → ℝ)
    (ωz : FieldPair d × CoupledSample d) (t : ℝ) : ℝ :=
  F ωz ((regenerationTime Δ lam R ωz.2 i 1).toNNReal + t.toNNReal) -
    F ωz (regenerationTime Δ lam R ωz.2 i 1).toNNReal

/-- The sum of profile increments is the increment to the last completed later cycle. -/
theorem sum_laterProfileReward {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (F : (FieldPair d × CoupledSample d) → ℝ≥0 → ℝ)
    (ωz : FieldPair d × CoupledSample d) (k : ℕ) :
    (∑ j ∈ range k, laterProfileReward Δ lam R i F j ωz) =
      F ωz (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal -
        F ωz (regenerationTime Δ lam R ωz.2 i 1).toNNReal := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih]
    simp only [laterProfileReward]
    ring

/-- Monotonicity brackets the increment of a profile by the sums through the completed and
next cycles. -/
theorem later_profile_bracket {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (F : (FieldPair d × CoupledSample d) → ℝ≥0 → ℝ)
    (ωz : FieldPair d × CoupledSample d) (hmono : Monotone (F ωz))
    (hfinite : ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤) (t : ℝ) (ht : 0 ≤ t) :
    (∑ j ∈ range (laterCount Δ hΔ lam R i ωz t), laterProfileReward Δ lam R i F j ωz) ≤
      laterProfilePosition Δ lam R i F ωz t ∧
    laterProfilePosition Δ lam R i F ωz t ≤
      ∑ j ∈ range (laterCount Δ hΔ lam R i ωz t + 1), laterProfileReward Δ lam R i F j ωz := by
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
  change (∑ j ∈ range k, laterProfileReward Δ lam R i F j ωz) ≤
    laterProfilePosition Δ lam R i F ωz t ∧
      laterProfilePosition Δ lam R i F ωz t ≤ ∑ j ∈ range (k + 1), laterProfileReward Δ lam R i F j ωz
  rw [sum_laterProfileReward, sum_laterProfileReward]
  dsimp only [laterProfilePosition]
  constructor <;> linarith [hmono hlow, hmono hupp]

/-- Independent integrable later-cycle increments of a monotone profile give its rate per
unit elapsed time. -/
theorem later_profile_rate_ae {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (F : (FieldPair d × CoupledSample d) → ℝ≥0 → ℝ)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤)
    (hmono : ∀ᵐ ωz ∂annealedCoupledLaw Q K, Monotone (F ωz))
    (ht : Integrable (laterDuration Δ lam R i 0) (annealedCoupledLaw Q K))
    (hit : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterDuration Δ lam R i))
    (hdt : ∀ n, IdentDistrib (laterDuration Δ lam R i n) (laterDuration Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hr : Integrable (laterProfileReward Δ lam R i F 0) (annealedCoupledLaw Q K))
    (hir : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterProfileReward Δ lam R i F))
    (hdr : ∀ n, IdentDistrib (laterProfileReward Δ lam R i F n) (laterProfileReward Δ lam R i F 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K)) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto
      (fun t : ℝ => laterProfilePosition Δ lam R i F ωz t / t) atTop
      (𝓝 ((∫ ωz, laterProfileReward Δ lam R i F 0 ωz ∂annealedCoupledLaw Q K) /
        ∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K)) := by
  have hbracket : ∀ᵐ ωz ∂annealedCoupledLaw Q K, ∀ᶠ t in atTop,
      (∑ j ∈ range (laterCount Δ hΔ lam R i ωz t), laterProfileReward Δ lam R i F j ωz) ≤
        laterProfilePosition Δ lam R i F ωz t ∧
      laterProfilePosition Δ lam R i F ωz t ≤
        ∑ j ∈ range (laterCount Δ hΔ lam R i ωz t + 1), laterProfileReward Δ lam R i F j ωz := by
    filter_upwards [hfinite, hmono] with ωz hf hmono'
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht0
    exact later_profile_bracket Δ hΔ lam R i F ωz hmono' hf t ht0
  simpa only [div_eq_mul_inv] using bracketed_reward_rate_ae (annealedCoupledLaw Q K)
    (laterProfileReward Δ lam R i F) (laterCount Δ hΔ lam R i) (laterProfilePosition Δ lam R i F)
    _ hr hir hdr (laterCount_tendsto_ae Q K Δ hΔ lam R i hfinite)
    (laterCount_rate_ae Q K hK Δ hΔ lam R i hfinite ht hit hdt) hbracket

end EinsteinFull.Regeneration
