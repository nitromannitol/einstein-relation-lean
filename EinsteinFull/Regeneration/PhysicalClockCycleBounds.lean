import EinsteinFull.Regeneration.PhysicalClockRate

/-!
# Physical-clock increments over regeneration cycles

The bounded potential bounds a clock increment by a constant times the length of its
cycle. Consequently, integrability of a cycle duration gives integrability of the
corresponding clock increment.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Physical-clock increments are bounded by elapsed time times the uniform density bound. -/
theorem physical_clock_increment_le {d : ℕ} (ω : FieldPair d) (γ : Path d) (L : ℝ)
    (hV : ∀ x, |ω.2 x| ≤ L) (s t : ℝ≥0) (hst : s ≤ t) :
    (Clock.physicalPathClock ω γ t : ℝ) - (Clock.physicalPathClock ω γ s : ℝ) ≤
      Real.exp (2 * L) * ((t : ℝ) - s) := by
  have hc := Clock.continuous_clockDensity_along ω γ
  have hT : IntervalIntegrable (fun u : ℝ => clockDensity ω (γ u.toNNReal)) volume 0 (t : ℝ) :=
    hc.intervalIntegrable _ _
  have hS : IntervalIntegrable (fun u : ℝ => clockDensity ω (γ u.toNNReal)) volume 0 (s : ℝ) :=
    hc.intervalIntegrable _ _
  have hdiff := intervalIntegral.integral_interval_sub_left hT hS
  have hbound := intervalIntegral.integral_mono_on (NNReal.coe_le_coe.mpr hst)
    (hc.intervalIntegrable (s : ℝ) (t : ℝ))
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.exp (2 * L)) volume (s : ℝ) (t : ℝ))
    (fun u _ => (clockDensity_bounds ω (γ u.toNNReal) L (hV _)).2)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hbound
  change (∫ u in (0 : ℝ)..(t : ℝ), clockDensity ω (γ u.toNNReal)) -
    (∫ u in (0 : ℝ)..(s : ℝ), clockDensity ω (γ u.toNNReal)) ≤ _
  nlinarith

/-- Evaluation of the physical clock at a measurable time is jointly measurable. -/
theorem measurable_physicalClock_at_regeneration {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (k : ℕ) : Measurable (fun ωz : FieldPair d × CoupledSample d =>
      physicalClockProfile ωz (regenerationTime Δ lam R ωz.2 i k).toNNReal) := by
  have hclock : Measurable (fun p : ℝ≥0 × (FieldPair d × CoupledSample d) =>
      physicalClockProfile p.2 p.1) := by
    change Measurable (Function.uncurry (fun t : ℝ≥0 =>
      fun ωz : FieldPair d × CoupledSample d => physicalClockProfile ωz t))
    apply measurable_uncurry_of_continuous_of_measurable
    · intro ωz
      exact NNReal.continuous_coe.comp
        (Clock.InverseMeaningV3.physicalPathClock_continuous ωz.1 ωz.2.1)
    · intro t
      exact (Clock.continuous_physicalPathClock_at t).measurable.comp
        (measurable_fst.prodMk measurable_snd.fst)
  have hτ := ((measurable_regenerationTime Δ lam R i k).comp
    (measurable_snd : Measurable (Prod.snd : FieldPair d × CoupledSample d → _))).ennreal_toNNReal
  exact hclock.comp (hτ.prodMk measurable_id)

/-- The physical-clock increment over each later regeneration cycle is measurable. -/
theorem measurable_later_physicalClockReward {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (k : ℕ) : Measurable (laterProfileReward Δ lam R i physicalClockProfile k) :=
  (measurable_physicalClock_at_regeneration Δ lam R i (k + 2)).sub
    (measurable_physicalClock_at_regeneration Δ lam R i (k + 1))

/-- The physical-clock reward is integrable whenever the later-cycle duration is integrable,
all regeneration times are finite, and the potential is bounded almost surely. -/
theorem integrable_later_physicalClockReward {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (Δ : ℝ≥0) (lam R L : ℝ) (i : Fin d)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤)
    (hV : ∀ᵐ ωz ∂annealedCoupledLaw Q K, ∀ x, |ωz.1.2 x| ≤ L)
    (ht : Integrable (laterDuration Δ lam R i 0) (annealedCoupledLaw Q K)) :
    Integrable (laterProfileReward Δ lam R i physicalClockProfile 0) (annealedCoupledLaw Q K) := by
  apply (ht.const_mul (Real.exp (2 * L))).mono'
    (measurable_later_physicalClockReward Δ lam R i 0).aestronglyMeasurable
  filter_upwards [hfinite, hV] with ωz hf hω
  have htime : (regenerationTime Δ lam R ωz.2 i 1).toNNReal ≤
      (regenerationTime Δ lam R ωz.2 i 2).toNNReal := by
    have h := regeneration_cycle_duration_ge Δ lam R ωz.2 i 1 (by simpa using hf 2)
    apply NNReal.coe_le_coe.mp
    simp only [ENNReal.coe_toNNReal_eq_toReal] at h ⊢
    have hΔ : 0 ≤ (Δ : ℝ) := Δ.property
    linarith
  have hnonneg : 0 ≤ laterProfileReward Δ lam R i physicalClockProfile 0 ωz := by
    change 0 ≤ (Clock.physicalPathClock ωz.1 ωz.2.1
      (regenerationTime Δ lam R ωz.2 i 2).toNNReal : ℝ) -
      (Clock.physicalPathClock ωz.1 ωz.2.1 (regenerationTime Δ lam R ωz.2 i 1).toNNReal : ℝ)
    exact sub_nonneg.mpr (Clock.physicalPathClock_mono (ωz.1, ωz.2.1) htime)
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  exact physical_clock_increment_le ωz.1 ωz.2.1 L hω _ _ htime

end EinsteinFull.Regeneration
