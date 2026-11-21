import EinsteinFull.Regeneration.LaterCoordinateVelocity

/-!
# Velocity from cycle laws with identically distributed maxima

The incomplete-cycle remainder is sublinear as soon as the cycle maxima are identically
distributed and integrable: by Borel–Cantelli, `M_n / n → 0` almost surely. Independence of
the maxima is not needed, so the maximal displacement over a cycle may depend on the final
bridge of the cycle.
-/

open MeasureTheory Filter Finset ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology ProbabilityTheory Function

namespace EinsteinFull.Regeneration

/-- An integrable sequence of identically distributed variables, divided by its index, tends to
zero almost surely (Borel–Cantelli). -/
theorem div_index_tendsto_zero_ae_of_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (M : ℕ → Ω → ℝ)
    (hm : Integrable (M 0) μ) (hdm : ∀ n, IdentDistrib (M n) (M 0) μ μ) :
    ∀ᵐ ω ∂μ, Tendsto (fun n : ℕ => M n ω / ((n : ℝ) + 1)) atTop (𝓝 0) := by
  have hk : ∀ k : ℕ, ∀ᵐ ω ∂μ, ∀ᶠ n : ℕ in atTop, ((k : ℝ) + 1) * |M n ω| ≤ n := by
    intro k
    set c : ℝ := (k : ℝ) + 1 with hc
    have hcpos : 0 < c := by positivity
    have hu : Measurable fun x : ℝ => c * |x| := measurable_const.mul continuous_abs.measurable
    let X : Ω → ℝ := fun ω => c * |M 0 ω|
    have hX : Integrable X μ := hm.abs.const_mul c
    have hX0 : 0 ≤ X := fun ω => mul_nonneg hcpos.le (abs_nonneg _)
    have hsum : (∑' j : ℕ, μ {ω | X ω ∈ Set.Ioi (j : ℝ)}) < ∞ := by
      let : MeasureSpace Ω := ⟨μ⟩
      exact tsum_prob_mem_Ioi_lt_top hX hX0
    have heq : ∀ n : ℕ, μ {ω | c * |M n ω| ∈ Set.Ioi (n : ℝ)} =
        μ {ω | X ω ∈ Set.Ioi (n : ℝ)} := fun n =>
      ((hdm n).comp hu).measure_mem_eq measurableSet_Ioi
    have hsum' : ∑' n : ℕ, μ {ω | c * |M n ω| ∈ Set.Ioi (n : ℝ)} ≠ ⊤ := by
      simp_rw [heq]
      exact hsum.ne
    filter_upwards [ae_eventually_notMem hsum'] with ω hω
    filter_upwards [hω] with n hn
    simpa only [Set.mem_ofPred_eq, Set.mem_Ioi, not_lt] using hn
  filter_upwards [ae_all_iff.2 hk] with ω hω
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨k, hkε⟩ := exists_nat_one_div_lt hε
  obtain ⟨N, hN⟩ := eventually_atTop.1 (hω k)
  refine ⟨N, fun n hn => ?_⟩
  have hb := hN n hn
  have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hn1, div_lt_iff₀ hn1]
  have h1 : |M n ω| ≤ (n : ℝ) / ((k : ℝ) + 1) := by
    rw [le_div_iff₀ hk1]
    linarith
  calc |M n ω| ≤ (n : ℝ) / ((k : ℝ) + 1) := h1
    _ ≤ ((n : ℝ) + 1) * (1 / ((k : ℝ) + 1)) := by
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right (by linarith) hk1.le
    _ < ((n : ℝ) + 1) * ε := mul_lt_mul_of_pos_left hkε hn1
    _ = ε * ((n : ℝ) + 1) := mul_comm _ _

/-- Integrable identically distributed cycle maxima make a dominated incomplete-cycle remainder
sublinear when the cycle count has a finite asymptotic rate. -/
theorem remainder_div_time_tendsto_zero_ae_of_identDistrib {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (maxima : ℕ → Ω → ℝ) (count : Ω → ℝ → ℕ)
    (remainder : Ω → ℝ → ℝ) (ν : ℝ)
    (hm : Integrable (maxima 0) μ)
    (hdm : ∀ n, IdentDistrib (maxima n) (maxima 0) μ μ)
    (hcount : ∀ᵐ ω ∂μ, Tendsto (count ω) atTop atTop)
    (hrate : ∀ᵐ ω ∂μ, Tendsto (fun t : ℝ => (count ω t : ℝ) / t) atTop (𝓝 ν))
    (hbound : ∀ᵐ ω ∂μ, ∀ᶠ t in atTop, |remainder ω t| ≤ maxima (count ω t) ω) :
    ∀ᵐ ω ∂μ, Tendsto (fun t : ℝ => remainder ω t / t) atTop (𝓝 0) := by
  filter_upwards [div_index_tendsto_zero_ae_of_identDistrib μ maxima hm hdm,
    hcount, hrate, hbound] with ω hmax hc ht hb
  have hfac : Tendsto (fun t : ℝ => ((count ω t : ℝ) + 1) / t) atTop (𝓝 ν) := by
    simpa only [add_div, one_div, add_zero] using ht.add tendsto_inv_atTop_zero
  have hg : Tendsto (fun t : ℝ =>
      (maxima (count ω t) ω / ((count ω t : ℝ) + 1)) *
        (((count ω t : ℝ) + 1) / t)) atTop (𝓝 0) := by
    simpa only [Function.comp_apply, zero_mul] using (hmax.comp hc).mul hfac
  have hle : ∀ᶠ t in atTop, |remainder ω t / t| ≤
      (maxima (count ω t) ω / ((count ω t : ℝ) + 1)) *
        (((count ω t : ℝ) + 1) / t) := by
    filter_upwards [hb, eventually_gt_atTop 0] with t hbt ht0
    have hn : (count ω t : ℝ) + 1 ≠ 0 := by positivity
    have hcalc : maxima (count ω t) ω / t =
        (maxima (count ω t) ω / ((count ω t : ℝ) + 1)) *
          (((count ω t : ℝ) + 1) / t) := by
      field_simp
    rw [abs_div, abs_of_pos ht0, ← hcalc]
    exact div_le_div_of_nonneg_right hbt ht0.le
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' (by simpa using hg.neg) hg
  · filter_upwards [hle] with t h
    exact (abs_le.mp h).1
  · filter_upwards [hle] with t h
    exact (abs_le.mp h).2

/-- Under the later-cycle laws and an integrable identically distributed coordinate maximum,
the original coupled path has the corresponding coordinate velocity. -/
theorem coupled_later_coordinate_velocity_of_identDistrib_maxima {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i j : Fin d)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤)
    (hr : Integrable (laterCoordinateReward Δ lam R i j 0) (annealedCoupledLaw Q K))
    (ht : Integrable (laterDuration Δ lam R i 0) (annealedCoupledLaw Q K))
    (hir : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterCoordinateReward Δ lam R i j))
    (hit : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterDuration Δ lam R i))
    (hdr : ∀ n, IdentDistrib (laterCoordinateReward Δ lam R i j n)
      (laterCoordinateReward Δ lam R i j 0) (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hdt : ∀ n, IdentDistrib (laterDuration Δ lam R i n) (laterDuration Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hm : Integrable (laterCoordinateMaximum Δ lam R i j 0) (annealedCoupledLaw Q K))
    (hdm : ∀ n, IdentDistrib (laterCoordinateMaximum Δ lam R i j n)
      (laterCoordinateMaximum Δ lam R i j 0) (annealedCoupledLaw Q K) (annealedCoupledLaw Q K)) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto
      (fun t : ℝ≥0 => (t : ℝ)⁻¹ * ωz.2.1 t j) atTop
      (𝓝 ((∫ ωz, laterCoordinateReward Δ lam R i j 0 ωz ∂annealedCoupledLaw Q K) /
        ∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K)) := by
  have : IsProbabilityMeasure (annealedCoupledLaw Q K) :=
    annealedCoupledLaw_isProbabilityMeasure Q K hK
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
  have hrem := remainder_div_time_tendsto_zero_ae_of_identDistrib (annealedCoupledLaw Q K)
    (laterCoordinateMaximum Δ lam R i j) (laterCount Δ hΔ lam R i)
    (fun ωz t => laterCoordinatePosition Δ lam R i j ωz t -
      ∑ a ∈ range (laterCount Δ hΔ lam R i ωz t), laterCoordinateReward Δ lam R i j a ωz)
    _ hm hdm hcount hrate hbound
  have hv := reward_rate_of_cycle_clock_ae (annealedCoupledLaw Q K)
    (laterCoordinateReward Δ lam R i j) (laterDuration Δ lam R i) (laterCount Δ hΔ lam R i)
    (laterCoordinatePosition Δ lam R i j) hr ht hir hit hdr hdt hmean hcount hbracket hrem
  filter_upwards [hv] with ωz hωz
  exact coordinate_velocity_of_time_shift ωz.2.1 j (regenerationTime Δ lam R ωz.2 i 1).toNNReal _
    hωz

/-- The source cycle laws imply a quenched vector velocity with a positive force component.
Durations and displacements of the later cycles are pairwise independent and identically
distributed; their coordinate maxima are identically distributed and integrable. -/
theorem quenched_velocity_of_later_cycle_laws_of_identDistrib_maxima {d : ℕ}
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
    (hdr : ∀ j n, IdentDistrib (laterCoordinateReward Δ lam R i j n)
      (laterCoordinateReward Δ lam R i j 0) (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hm : ∀ j, Integrable (laterCoordinateMaximum Δ lam R i j 0) (annealedCoupledLaw Q K))
    (hdm : ∀ j n, IdentDistrib (laterCoordinateMaximum Δ lam R i j n)
      (laterCoordinateMaximum Δ lam R i j 0) (annealedCoupledLaw Q K) (annealedCoupledLaw Q K)) :
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
    have h := coupled_later_coordinate_velocity_of_identDistrib_maxima Q K hK Δ hΔ lam R i j
      hfinite (hr j) ht (hir j) hit (hdr j) hdt (hm j) (hdm j)
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
