import EinsteinFull.Regeneration.LaterCycleVelocity

/-!
# Clock laws for later regeneration cycles

The delayed count and its bracket follow from finiteness of the literal regeneration times.
The positive mean duration follows from the grid spacing once integrability is established.
-/

open MeasureTheory Filter Finset ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal Topology ProbabilityTheory Function

namespace EinsteinFull.Regeneration

/-- Almost-sure finiteness of the regeneration times makes the later-cycle count diverge. -/
theorem laterCount_tendsto_ae {d : ℕ} (Q : Measure (FieldPair d))
    (K : CoupledQuenchedLaws d) (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, Tendsto (laterCount Δ hΔ lam R i ωz) atTop atTop := by
  filter_upwards [hfinite] with ωz hf
  have heq : laterCount Δ hΔ lam R i ωz = laterRegenerationCount Δ hΔ lam R ωz.2 i hf := by
    funext t
    simp only [laterCount, dite_eq_left hf]
  rw [heq]
  exact laterRegenerationCount_tendsto_atTop Δ hΔ lam R ωz.2 i hf

/-- The delayed count brackets elapsed time by the sums of the later-cycle durations. -/
theorem laterCount_bracket_ae {d : ℕ} (Q : Measure (FieldPair d))
    (K : CoupledQuenchedLaws d) (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K, ∀ᶠ t in atTop,
      (∑ j ∈ range (laterCount Δ hΔ lam R i ωz t), laterDuration Δ lam R i j ωz) ≤ t ∧
        t ≤ ∑ j ∈ range (laterCount Δ hΔ lam R i ωz t + 1), laterDuration Δ lam R i j ωz := by
  filter_upwards [hfinite] with ωz hf
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht0
  have h := laterRegenerationCount_bracket Δ hΔ lam R ωz.2 i hf t ht0
  simpa only [laterCount, dite_eq_left hf, laterDuration] using ⟨h.1, h.2.le⟩

/-- A finite integrable later-cycle duration has positive expectation. -/
theorem laterDuration_integral_pos {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤)
    (ht : Integrable (laterDuration Δ lam R i 0) (annealedCoupledLaw Q K)) :
    0 < ∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K := by
  have hfin2 : ∀ᵐ ωz ∂annealedCoupledLaw Q K, regenerationTime Δ lam R ωz.2 i (1 + 1) ≠ ⊤ :=
    hfinite.mono fun _ h => h _
  have ht' : Integrable (fun ωz : FieldPair d × CoupledSample d =>
      ((regenerationTime Δ lam R ωz.2 i (1 + 1)).toNNReal : ℝ) -
        (regenerationTime Δ lam R ωz.2 i 1).toNNReal) (annealedCoupledLaw Q K) := ht
  exact regeneration_cycle_expected_duration_pos Q K hK Δ hΔ lam R i 1 hfin2 ht'

/-- The delayed cycle count has the reciprocal mean-duration rate under the strong law. -/
theorem laterCount_rate_ae {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (i : Fin d)
    (hfinite : ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      ∀ k, regenerationTime Δ lam R ωz.2 i k ≠ ⊤)
    (ht : Integrable (laterDuration Δ lam R i 0) (annealedCoupledLaw Q K))
    (hit : Pairwise ((· ⟂ᵢ[annealedCoupledLaw Q K] ·) on laterDuration Δ lam R i))
    (hdt : ∀ n, IdentDistrib (laterDuration Δ lam R i n) (laterDuration Δ lam R i 0)
      (annealedCoupledLaw Q K) (annealedCoupledLaw Q K)) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q K,
      Tendsto (fun t : ℝ => (laterCount Δ hΔ lam R i ωz t : ℝ) / t) atTop
        (𝓝 (∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K)⁻¹) := by
  have hmean := laterDuration_integral_pos Q K hK Δ hΔ lam R i hfinite ht
  filter_upwards [strong_law_ae (laterDuration Δ lam R i) ht hit hdt,
    laterCount_tendsto_ae Q K Δ hΔ lam R i hfinite,
    laterCount_bracket_ae Q K Δ hΔ lam R i hfinite] with ωz hs hc hb
  have hclock : Tendsto (fun n : ℕ => (∑ j ∈ range n, laterDuration Δ lam R i j ωz) / (n : ℝ))
      atTop (𝓝 (∫ ωz, laterDuration Δ lam R i 0 ωz ∂annealedCoupledLaw Q K)) := by
    simpa only [smul_eq_mul, div_eq_mul_inv, mul_comm] using hs
  exact cycle_count_rate_of_clock (fun n => ∑ j ∈ range n, laterDuration Δ lam R i j ωz)
    (laterCount Δ hΔ lam R i ωz) _ hmean hclock hc hb

end EinsteinFull.Regeneration
