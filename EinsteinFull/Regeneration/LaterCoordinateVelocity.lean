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

/-- The later-cycle coordinate reward is measurable. -/
theorem measurable_laterCoordinateReward {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i j : Fin d) (k : ℕ) : Measurable (laterCoordinateReward Δ lam R i j k) := by
  have hτ (n : ℕ) := ((measurable_regenerationTime Δ lam R i n).comp
    (measurable_snd : Measurable (Prod.snd : FieldPair d × CoupledSample d → _))).ennreal_toNNReal
  have hx (n : ℕ) := measurable_path_eval.comp ((hτ n).prodMk measurable_snd.fst)
  exact ((measurable_pi_apply j).comp (hx (k + 2))).sub ((measurable_pi_apply j).comp (hx (k + 1)))

/-- The absolute coordinate reward of a finite cycle is bounded by that cycle's maximum. -/
theorem later_coordinate_reward_le_maximum {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i j : Fin d) (k : ℕ) (ωz : FieldPair d × CoupledSample d)
    (hfin : regenerationTime Δ lam R ωz.2 i (k + 2) ≠ ⊤) :
    |laterCoordinateReward Δ lam R i j k ωz| ≤ laterCoordinateMaximum Δ lam R i j k ωz := by
  have htime : (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal ≤
      (regenerationTime Δ lam R ωz.2 i (k + 2)).toNNReal := by
    have h := regeneration_cycle_duration_ge Δ lam R ωz.2 i (k + 1) (by simpa [Nat.add_assoc] using hfin)
    apply NNReal.coe_le_coe.mp
    simp only [ENNReal.coe_toNNReal_eq_toReal] at h ⊢
    have hΔ : 0 ≤ (Δ : ℝ) := Δ.property
    linarith
  exact displacement_le_interval_maximum ωz.2.1 j
    (regenerationTime Δ lam R ωz.2 i (k + 1)).toNNReal
    (regenerationTime Δ lam R ωz.2 i (k + 2)).toNNReal
    (regenerationTime Δ lam R ωz.2 i (k + 2)).toNNReal htime le_rfl

/-- Integrability of the later-cycle maximum implies integrability of its coordinate reward. -/
theorem integrable_laterCoordinateReward_of_maximum {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d) (Δ : ℝ≥0) (lam R : ℝ)
    (i j : Fin d) (k : ℕ)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K, regenerationTime Δ lam R ωz.2 i (k + 2) ≠ ⊤)
    (hm : Integrable (laterCoordinateMaximum Δ lam R i j k) (annealedCoupledLaw Q K)) :
    Integrable (laterCoordinateReward Δ lam R i j k) (annealedCoupledLaw Q K) := by
  apply hm.mono (measurable_laterCoordinateReward Δ lam R i j k).aestronglyMeasurable
  filter_upwards [hfinite] with ωz hfin
  simp only [Real.norm_eq_abs]
  exact (later_coordinate_reward_le_maximum Δ lam R i j k ωz hfin).trans (le_abs_self _)

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

/-- The source cycle laws imply a quenched vector velocity with a positive force component.
The finiteness, independence and moment statements for the literal cycles are explicit. -/
theorem quenched_velocity_of_later_cycle_laws {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (hpath : HasPathMarginals Q K P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (i : Fin d) (hsupport : HasSuccessfulBridgeSupport Q Δ i R K)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤)
    (ht : Integrable (laterDuration Δ lam R i 0) (annealedCoupledLaw Q K))
    (hit : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterDuration Δ lam R i))
    (hdt : ∀ n, IdentDistrib (laterDuration Δ lam R i n) (laterDuration Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hir : ∀ j, Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterCoordinateReward Δ lam R i j))
    (hdr : ∀ j n, IdentDistrib (laterCoordinateReward Δ lam R i j n) (laterCoordinateReward Δ lam R i j 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hm : ∀ j, Integrable (laterCoordinateMaximum Δ lam R i j 0) (annealedCoupledLaw Q K))
    (him : ∀ j, Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterCoordinateMaximum Δ lam R i j))
    (hdm : ∀ j n, IdentDistrib (laterCoordinateMaximum Δ lam R i j n) (laterCoordinateMaximum Δ lam R i j 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K)) :
    ∃ v : Vec d, HasQuenchedVelocity Q (originLaw P) v ∧ 0 < v i := by
  have hr : ∀ j, Integrable (laterCoordinateReward Δ lam R i j 0) (annealedCoupledLaw Q K) := by
    intro j
    apply integrable_laterCoordinateReward_of_maximum Q K Δ lam R i j 0
    · exact hfinite.mono fun _ h => h _
    · exact hm j
  let v : Vec d := fun j =>
    (∫ ωz, laterCoordinateReward Δ lam R i j 0 ωz ∂annealedCoupledLaw Q K) /
      ∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K
  have hv : HasQuenchedVelocity Q (originLaw P) v := by
    apply quenched_velocity_of_coordinates
    intro j
    have h := coupled_later_coordinate_velocity Q K hK Δ hΔ lam R i j hfinite
      (hr j) ht (hir j) hit (hdr j) hdt (hm j) (him j) (hdm j)
    exact quenched_coordinate_velocity_of_annealed Q P K hK hpath j (v j) h
  have hfin2 : ∀ᵐ ωz ∂annealedCoupledLaw Q K, regenerationTime Δ lam R ωz.2 i (1 + 1) ≠ ⊤ :=
    hfinite.mono fun _ h => h _
  have hr' : Integrable (fun ωz : FieldPair d × CoupledSample d =>
      ωz.2.1 (regenerationTime Δ lam R ωz.2 i (1 + 1)).toNNReal i -
        ωz.2.1 (regenerationTime Δ lam R ωz.2 i 1).toNNReal i) (annealedCoupledLaw Q K) := hr i
  have hmeanR : 0 < ∫ ωz, laterCoordinateReward Δ lam R i i 0 ωz ∂annealedCoupledLaw Q K :=
    regeneration_cycle_expected_displacement_pos Q K hK Δ hΔ lam R hlam hR i hsupport 1 hfin2 hr'
  have hmeanT := laterDuration_integral_pos Q K hK Δ hΔ lam R i hfinite ht
  exact ⟨v, hv, div_pos hmeanR hmeanT⟩

end EinsteinFull.Regeneration
