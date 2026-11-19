import EinsteinFull.Regeneration.DelayedRegenerationCount
import EinsteinFull.Regeneration.RegenerationCycleProgress
import EinsteinFull.Regeneration.RewardStrongLaw

/-!
# Velocity from later regeneration cycles

The initial regeneration interval may differ in law from the later cycles. Starting the
clock at the first regeneration gives the ratio in Gantert–Mathieu–Piatnitski,
Proposition 5.9, once the later-cycle independence, moments and remainder estimate are
established.
-/

open MeasureTheory Filter Finset ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology ProbabilityTheory Function

namespace EinsteinFull.Regeneration

/-- Later-cycle durations as random variables on environment and coupled sample. -/
noncomputable def laterDuration {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (k : ℕ) (ωz : FieldPair d × CoupledSample d) : ℝ :=
  laterCycleDuration Δ lam R ωz.2 i k

/-- Later-cycle force-coordinate displacements as random variables. -/
noncomputable def laterReward {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (k : ℕ) (ωz : FieldPair d × CoupledSample d) : ℝ :=
  ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 2)).toNNReal i -
    ωz.2.1 (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal i

/-- Displacement from the first regeneration at the given elapsed time. -/
noncomputable def laterPosition {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (ωz : FieldPair d × CoupledSample d) (t : ℝ) : ℝ :=
  ωz.2.1 ((regenerationTime Δ lam R ωz.2 i 1).toNNReal + t.toNNReal) i -
    ωz.2.1 (regenerationTime Δ lam R ωz.2 i 1).toNNReal i

/-- The completed later-cycle count, defined everywhere and using the literal count when all
regeneration times are finite. -/
noncomputable def laterCount {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (ωz : FieldPair d × CoupledSample d) (t : ℝ) : ℕ := by
  classical
  exact if h : ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤ then
    laterRegenerationCount Δ hΔ lam R ωz.2 i h t else 0

/-- A velocity after a finite time shift is also the velocity of the original path. -/
theorem coordinate_velocity_of_time_shift {d : ℕ} (γ : Path d) (i : Fin d) (S : ℝ≥0) (v : ℝ)
    (h : Tendsto (fun t : ℝ => (γ (S + t.toNNReal) i - γ S i) / t) atTop (𝓝 v)) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * γ t i) atTop (𝓝 v) := by
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have htime : Tendsto (fun t : ℝ≥0 => (t : ℝ) - S) atTop atTop := by
    simpa only [sub_eq_add_neg] using tendsto_atTop_add_const_right _ (-(S : ℝ)) hcoe
  have hinv : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hcoe
  have hfactor : Tendsto (fun t : ℝ≥0 => ((t : ℝ) - S) / t) atTop (𝓝 1) := by
    have h' := (tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (1 : ℝ)) atTop (𝓝 1)).sub
      (hinv.const_mul (S : ℝ))
    have h'' : Tendsto (fun t : ℝ≥0 => 1 - (S : ℝ) * (t : ℝ)⁻¹) atTop (𝓝 1) := by
      simpa using h'
    apply h''.congr'
    filter_upwards [hcoe.eventually_gt_atTop 0] with t ht
    have ht' : (t : ℝ) ≠ 0 := ne_of_gt ht
    field_simp
  have hconst : Tendsto (fun t : ℝ≥0 => γ S i / (t : ℝ)) atTop (𝓝 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hinv.const_mul (γ S i)
  have htotal := ((h.comp htime).mul hfactor).add hconst
  have htotal' : Tendsto (fun t : ℝ≥0 =>
      ((γ (S + ((t : ℝ) - S).toNNReal) i - γ S i) / ((t : ℝ) - S)) *
        (((t : ℝ) - S) / (t : ℝ)) + γ S i / (t : ℝ)) atTop (𝓝 v) := by
    simpa only [Function.comp_apply, mul_one, add_zero] using htotal
  apply htotal'.congr'
  filter_upwards [hcoe.eventually_gt_atTop (S : ℝ), hcoe.eventually_gt_atTop 0] with t ht ht0
  have hst : (S : ℝ) ≤ (t : ℝ) := ht.le
  have hsum : S + ((t : ℝ) - S).toNNReal = t := by
    apply NNReal.eq
    rw [NNReal.coe_add, Real.coe_toNNReal _ (sub_nonneg.mpr hst)]
    ring
  rw [hsum]
  have hden : (t : ℝ) - S ≠ 0 := ne_of_gt (sub_pos.mpr ht)
  have ht' : (t : ℝ) ≠ 0 := ne_of_gt ht0
  field_simp
  ring

/-- An almost-sure elapsed-time velocity transfers to the original coupled path. -/
theorem ae_coordinate_velocity_of_later_velocity {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (v : ℝ)
    (h : ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto
      (fun t : ℝ => laterPosition Δ lam R i ωz t / t) atTop (𝓝 v)) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto
      (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ωz.2.1 t i) atTop (𝓝 v) := by
  filter_upwards [h] with ωz hωz
  exact coordinate_velocity_of_time_shift ωz.2.1 i
    (regenerationTime Δ lam R ωz.2 i 1).toNNReal v hωz

/-- The literal later cycles give a positive renewal velocity once their independence,
integrability, finiteness and incomplete-cycle estimate have been established. -/
theorem later_regeneration_velocity_ae {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i R K)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤)
    (hr : Integrable (laterReward Δ lam R i 0) (annealedCoupledLaw Q K))
    (ht : Integrable (laterDuration Δ lam R i 0) (annealedCoupledLaw Q K))
    (hir : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterReward Δ lam R i))
    (hit : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterDuration Δ lam R i))
    (hdr : ∀ n, IdentDistrib (laterReward Δ lam R i n) (laterReward Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hdt : ∀ n, IdentDistrib (laterDuration Δ lam R i n) (laterDuration Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hrem : ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto
      (fun t : ℝ => (laterPosition Δ lam R i ωz t -
        ∑ j ∈ range (laterCount Δ hΔ lam R i ωz t), laterReward Δ lam R i j ωz) / t)
      atTop (𝓝 0)) :
    0 < (∫ ωz, laterReward Δ lam R i 0 ωz ∂annealedCoupledLaw Q K) /
      (∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K) ∧
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto
      (fun t : ℝ => laterPosition Δ lam R i ωz t / t) atTop
      (𝓝 ((∫ ωz, laterReward Δ lam R i 0 ωz ∂annealedCoupledLaw Q K) /
        ∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K)) := by
  have hfin2 : ∀ᵐ ωz ∂annealedCoupledLaw Q K, regenerationTime Δ lam R ωz.2 i (1 + 1) ≠ ⊤ :=
    hfinite.mono fun _ h => h _
  have ht' : Integrable (fun ωz : FieldPair d × CoupledSample d =>
      ((regenerationTime Δ lam R ωz.2 i (1 + 1)).toNNReal : ℝ) -
        (regenerationTime Δ lam R ωz.2 i 1).toNNReal) (annealedCoupledLaw Q K) := by
    exact ht
  have hmeanT : 0 < ∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K := by
    exact regeneration_cycle_expected_duration_pos Q K hK Δ hΔ lam R i 1 hfin2 ht'
  have hr' : Integrable (fun ωz : FieldPair d × CoupledSample d =>
      ωz.2.1 (regenerationTime Δ lam R ωz.2 i (1 + 1)).toNNReal i -
        ωz.2.1 (regenerationTime Δ lam R ωz.2 i 1).toNNReal i) (annealedCoupledLaw Q K) := by
    exact hr
  have hmeanR : 0 < ∫ ωz, laterReward Δ lam R i 0 ωz ∂annealedCoupledLaw Q K := by
    exact regeneration_cycle_expected_displacement_pos Q K hK Δ hΔ lam R hlam hR i hsupport 1 hfin2 hr'
  have hcount : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      Tendsto (laterCount Δ hΔ lam R i ωz) atTop atTop := by
    filter_upwards [hfinite] with ωz hf
    have heq : laterCount Δ hΔ lam R i ωz = laterRegenerationCount Δ hΔ lam R ωz.2 i hf := by
      funext t
      simp only [laterCount, dite_eq_left hf]
    rw [heq]
    exact laterRegenerationCount_tendsto_atTop Δ hΔ lam R ωz.2 i hf
  have hbracket : ∀ᵐ ωz ∂annealedCoupledLaw Q K, ∀ᶠ t in atTop,
      (∑ j ∈ range (laterCount Δ hΔ lam R i ωz t), laterDuration Δ lam R i j ωz) ≤ t ∧
        t ≤ ∑ j ∈ range (laterCount Δ hΔ lam R i ωz t + 1), laterDuration Δ lam R i j ωz := by
    filter_upwards [hfinite] with ωz hf
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht0
    have h := laterRegenerationCount_bracket Δ hΔ lam R ωz.2 i hf t ht0
    simpa only [laterCount, dite_eq_left hf, laterDuration] using ⟨h.1, h.2.le⟩
  refine ⟨div_pos hmeanR hmeanT, ?_⟩
  exact reward_rate_of_cycle_clock_ae (annealedCoupledLaw Q K) (laterReward Δ lam R i)
    (laterDuration Δ lam R i) (laterCount Δ hΔ lam R i) (laterPosition Δ lam R i)
    hr ht hir hit hdr hdt hmeanT hcount hbracket hrem

end EinsteinFull.Regeneration
