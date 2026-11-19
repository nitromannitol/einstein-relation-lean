import EinsteinFull.Regeneration.LaterCycleVelocity

/-!
# The incomplete later cycle

The path displacement remaining after the last completed regeneration cycle is bounded by
the maximum displacement within that cycle. This supplies the pathwise remainder estimate
in the renewal argument of Gantert–Mathieu–Piatnitski, Proposition 5.9.
-/

open MeasureTheory Filter Finset ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology ProbabilityTheory Function

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

/-- Integrable independent later-cycle maxima make the literal incomplete-cycle remainder
sublinear, once later-cycle durations satisfy the strong law. -/
theorem later_regeneration_remainder_sublinear_ae {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤)
    (ht : Integrable (laterDuration Δ lam R i 0) (annealedCoupledLaw Q K))
    (hit : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterDuration Δ lam R i))
    (hdt : ∀ n, IdentDistrib (laterDuration Δ lam R i n) (laterDuration Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hm : Integrable (laterCycleMaximum Δ lam R i 0) (annealedCoupledLaw Q K))
    (him : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterCycleMaximum Δ lam R i))
    (hdm : ∀ n, IdentDistrib (laterCycleMaximum Δ lam R i n) (laterCycleMaximum Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K)) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto
      (fun t : ℝ => (laterPosition Δ lam R i ωz t -
        ∑ j ∈ range (laterCount Δ hΔ lam R i ωz t), laterReward Δ lam R i j ωz) / t)
      atTop (𝓝 0) := by
  have hfin2 : ∀ᵐ ωz ∂annealedCoupledLaw Q K, regenerationTime Δ lam R ωz.2 i (1 + 1) ≠ ⊤ :=
    hfinite.mono fun _ h => h _
  have ht' : Integrable (fun ωz : FieldPair d × CoupledSample d =>
      ((regenerationTime Δ lam R ωz.2 i (1 + 1)).toNNReal : ℝ) -
        (regenerationTime Δ lam R ωz.2 i 1).toNNReal) (annealedCoupledLaw Q K) := ht
  have hmean : 0 < ∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K :=
    regeneration_cycle_expected_duration_pos Q K hK Δ hΔ lam R i 1 hfin2 ht'
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
  have hrate : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      Tendsto (fun t : ℝ => (laterCount Δ hΔ lam R i ωz t : ℝ) / t) atTop
        (𝓝 (∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K)⁻¹) := by
    filter_upwards [strong_law_ae (laterDuration Δ lam R i) ht hit hdt, hcount, hbracket]
      with ωz hs hc hb
    have hclock : Tendsto (fun n : ℕ => (∑ j ∈ range n, laterDuration Δ lam R i j ωz) / (n : ℝ))
        atTop (𝓝 (∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K)) := by
      simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hs
    exact cycle_count_rate_of_clock (fun n => ∑ j ∈ range n, laterDuration Δ lam R i j ωz)
      (laterCount Δ hΔ lam R i ωz) _ hmean hclock hc hb
  have hbound : ∀ᵐ ωz ∂annealedCoupledLaw Q K, ∀ᶠ t in atTop,
      |laterPosition Δ lam R i ωz t -
        ∑ j ∈ range (laterCount Δ hΔ lam R i ωz t), laterReward Δ lam R i j ωz| ≤
          laterCycleMaximum Δ lam R i (laterCount Δ hΔ lam R i ωz t) ωz := by
    filter_upwards [hfinite] with ωz hf
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht0
    exact later_regeneration_remainder_le_maximum Δ hΔ lam R i ωz hf t ht0
  exact remainder_div_time_tendsto_zero_ae (annealedCoupledLaw Q K)
    (laterCycleMaximum Δ lam R i) (laterCount Δ hΔ lam R i)
    (fun ωz t => laterPosition Δ lam R i ωz t -
      ∑ j ∈ range (laterCount Δ hΔ lam R i ωz t), laterReward Δ lam R i j ωz)
    _ hm him hdm hcount hrate hbound

/-- Literal later-cycle laws and integrable independent cycle maxima imply a positive
force-coordinate velocity of the original coupled path. -/
theorem coupled_coordinate_velocity_of_cycle_laws {d : ℕ}
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
    (hm : Integrable (laterCycleMaximum Δ lam R i 0) (annealedCoupledLaw Q K))
    (him : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterCycleMaximum Δ lam R i))
    (hdm : ∀ n, IdentDistrib (laterCycleMaximum Δ lam R i n) (laterCycleMaximum Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K)) :
    0 < (∫ ωz, laterReward Δ lam R i 0 ωz ∂annealedCoupledLaw Q K) /
      (∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K) ∧
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto
      (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ωz.2.1 t i) atTop
      (𝓝 ((∫ ωz, laterReward Δ lam R i 0 ωz ∂annealedCoupledLaw Q K) /
        ∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K)) := by
  have hrem := later_regeneration_remainder_sublinear_ae Q K hK Δ hΔ lam R i
    hfinite ht hit hdt hm him hdm
  have hv := later_regeneration_velocity_ae Q K hK Δ hΔ lam R hlam hR i hsupport
    hfinite hr ht hir hit hdr hdt hrem
  exact ⟨hv.1, ae_coordinate_velocity_of_later_velocity Q K Δ lam R i _ hv.2⟩

end EinsteinFull.Regeneration
