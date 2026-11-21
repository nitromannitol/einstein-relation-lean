import EinsteinFull.Regeneration.LaterProfileRate
import EinsteinFull.Regeneration.PhysicalVelocityTransfer
import EinsteinRelation.Clock.ClockExpectation

/-!
# Physical-clock rate from regeneration cycles

The physical clock is increasing. Its rate follows from the strong law for its increments
between later regeneration times and the strong law for the cycle durations. The necessary
cycle laws remain explicit hypotheses.
-/

open MeasureTheory Filter Finset ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology ProbabilityTheory Function

namespace EinsteinFull.Regeneration

/-- The physical clock of an environment and a coupled path. -/
noncomputable def physicalClockProfile {d : ℕ}
    (ωz : FieldPair d × CoupledSample d) (t : ℝ≥0) : ℝ :=
  Clock.physicalPathClock ωz.1 ωz.2.1 t

/-- A physical-clock strong law follows from the later-cycle clock-increment laws. -/
theorem annealed_physical_clock_rate_of_cycle_laws {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤)
    (ht : Integrable (laterDuration Δ lam R i 0) (annealedCoupledLaw Q K))
    (hit : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterDuration Δ lam R i))
    (hdt : ∀ n, IdentDistrib (laterDuration Δ lam R i n) (laterDuration Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K))
    (hr : Integrable (laterProfileReward Δ lam R i physicalClockProfile 0) (annealedCoupledLaw Q K))
    (hir : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterProfileReward Δ lam R i physicalClockProfile))
    (hdr : ∀ n, IdentDistrib (laterProfileReward Δ lam R i physicalClockProfile n)
      (laterProfileReward Δ lam R i physicalClockProfile 0) (annealedCoupledLaw Q K) (annealedCoupledLaw Q K)) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto
      (fun t : ℝ≥0 => (Clock.physicalPathClock ωz.1 ωz.2.1 t : ℝ) / t) atTop
      (𝓝 ((∫ ωz, laterProfileReward Δ lam R i physicalClockProfile 0 ωz ∂annealedCoupledLaw Q K) /
        ∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K)) := by
  have hmono : ∀ᵐ ωz ∂annealedCoupledLaw Q K, Monotone (physicalClockProfile ωz) := by
    filter_upwards with ωz a b hab
    exact Clock.physicalPathClock_mono (ωz.1, ωz.2.1) hab
  have h := later_profile_rate_ae Q K hK Δ hΔ lam R i physicalClockProfile
    hfinite hmono ht hit hdt hr hir hdr
  filter_upwards [h] with ωz hωz
  have hc : Continuous (physicalClockProfile ωz) :=
    NNReal.continuous_coe.comp (Clock.InverseMeaningV3.physicalPathClock_continuous ωz.1 ωz.2.1)
  let γ : Path 1 := ⟨fun t _ => physicalClockProfile ωz t, continuous_pi fun _ => hc⟩
  have hv := coordinate_velocity_of_time_shift γ (0 : Fin 1)
    (regenerationTime Δ lam R ωz.2 i 1).toNNReal _ hωz
  change Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ *
    (Clock.physicalPathClock ωz.1 ωz.2.1 t : ℝ)) atTop _ at hv
  simpa only [div_eq_mul_inv, mul_comm] using hv

/-- The physical clock-rate event is measurable for each fixed environment. -/
theorem measurableSet_physical_clock_rate {d : ℕ} (ω : FieldPair d) (η : ℝ) :
    MeasurableSet {γ : Path d | Tendsto
      (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 η)} := by
  have heq : {γ : Path d | Tendsto
      (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 η)} =
      (fun γ : Path d => (ω, γ)) ⁻¹' Clock.clockRateNatSet η := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage, Clock.clockRateNatSet]
    constructor
    · intro h
      exact h.comp tendsto_natCast_atTop_atTop
    · intro h
      apply Clock.tendsto_div_of_tendsto_natCast (fun _ => NNReal.coe_nonneg _)
      · intro a b hab
        exact Clock.physicalPathClock_mono (ω, γ) hab
      · exact h
  rw [heq]
  exact (Clock.measurableSet_clockRateNatSet η).preimage (measurable_const.prodMk measurable_id)

/-- The actual coupling's path marginal transfers an annealed clock rate to the quenched
origin path laws. -/
theorem quenched_physical_clock_rate_of_annealed {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (hpath : HasPathMarginals Q K P) (η : ℝ)
    (hclock : ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto
      (fun t : ℝ≥0 => (Clock.physicalPathClock ωz.1 ωz.2.1 t : ℝ) / t) atTop (𝓝 η)) :
    ∀ᵐ ω ∂Q, ∀ᵐ γ ∂P (0, ω), Tendsto
      (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 η) := by
  have hdis := Measure.ae_ae_of_ae_compProd hclock
  filter_upwards [hK.1, hpath.1, hdis] with ω hprob hmap hω
  have : IsProbabilityMeasure (originCoupledLaw K ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω] at hω
  rw [← hmap]
  exact (ae_map_iff measurable_fst.aemeasurable (measurableSet_physical_clock_rate ω η)).mpr hω

/-- A deterministic quenched physical-clock rate is strictly positive for bounded-potential
environments and probability path laws. -/
theorem physical_clock_rate_pos {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (P : ProbabilityTheory.Kernel (FieldPair d) (Path d)) (L η : ℝ)
    (hreg : ∀ᵐ ω ∂Q, IsRegular L ω)
    (hprob : ∀ᵐ ω ∂Q, IsProbabilityMeasure (P ω))
    (hclock : ∀ᵐ ω ∂Q, ∀ᵐ γ ∂P ω, Tendsto
      (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 η)) :
    0 < η := by
  obtain ⟨ω, hω, hωprob, hωclock⟩ := (hreg.and (hprob.and hclock)).exists
  have : IsProbabilityMeasure (P ω) := hωprob
  obtain ⟨γ, hγ⟩ := hωclock.exists
  have hbound : ∀ᶠ t : ℝ≥0 in atTop, Real.exp (-2 * L) ≤
      (Clock.physicalPathClock ω γ t : ℝ) / t := by
    filter_upwards [eventually_ge_atTop (1 : ℝ≥0)] with t ht
    have ht0 : 0 < (t : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one ht)
    exact (le_div_iff₀ ht0).2 (Clock.InverseMeaningV3.physicalPathClock_bounds ω γ L hω.2.1 t).1
  exact lt_of_lt_of_le (Real.exp_pos _) (ge_of_tendsto hγ hbound)

end EinsteinFull.Regeneration
