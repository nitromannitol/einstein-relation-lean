import EinsteinRelation.Probability.FiniteHistoryMeasurability
import EinsteinRelation.Probability.DowncrossingEvents

/-! # The bounded-horizon past barrier is measurable for the exact finite history

Source `paper/main.tex:412–420`, Step 4. On `{τ₁ = nΔ}` the event `𝒟` coincides with the
past barrier `{∀ s ∈ [0, (n-1)Δ], e₁ · Y_s > -R}`, which is taken over a deterministic
sub-horizon `T ≤ mΔ` rather than over the whole window `[0, mΔ]`.

This generalizes `measurableSet_strict_past_barrier` (`StrictPastBarrier.lean`) to an
arbitrary deterministic horizon `T ≤ mΔ`. The barrier is the complement of the closed
finite-horizon downcrossing event on `[0, T]`, which is closed in path space by
`isClosed_downcrossing_by` for every `T`. The stopped extension at `m` agrees with the
sample on `[0, mΔ]`, hence on `[0, T]`, so the barrier is its own preimage and inherits
measurability from the exact finite-history sigma-algebra. No positivity, finite-hitting,
or stopping-time premise is used.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

/-- Source `paper/main.tex:412–420`, Step 4. For a deterministic sub-horizon `T ≤ mΔ`, the
past barrier `{∀ s ∈ [0, T], -R < e_i · (Y_s - Y_0)}` is measurable for the exact
finite-history sigma-algebra `finiteHistorySigma Δ m`. -/
theorem measurableSet_bounded_horizon_past_barrier {d : ℕ} (Δ : ℝ≥0) (m : ℕ)
    (T : ℝ≥0) (hT : T ≤ (m : ℝ≥0) * Δ) (R : ℝ) (i : Fin d) :
    @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ m)
      {z | ∀ s : ℝ≥0, s ≤ T → -R < z.1 s i - z.1 0 i} := by
  -- The barrier is the complement of the closed finite-horizon downcrossing event on `[0, T]`.
  have hcompl : {z : CoupledSample d | ∀ s : ℝ≥0, s ≤ T → -R < z.1 s i - z.1 0 i} =
      (Prod.fst ⁻¹' {γ : Path d |
        ∃ t ∈ Set.Icc (0 : ℝ≥0) T, γ t i - γ 0 i ≤ -R})ᶜ := by
    ext z
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_preimage]
    constructor
    · rintro h ⟨t, ht, hle⟩
      linarith [h t ht.2]
    · intro h t ht
      by_contra hcon
      exact h ⟨t, ⟨zero_le, ht⟩, not_lt.mp hcon⟩
  have hclosed := EinsteinRelation.Probability.isClosed_downcrossing_by i R T
  have hprod : MeasurableSet {z : CoupledSample d |
      ∀ s : ℝ≥0, s ≤ T → -R < z.1 s i - z.1 0 i} := by
    rw [hcompl]
    exact MeasurableSet.compl (hclosed.measurableSet.preimage measurable_fst)
  -- The stopped extension at `m` keeps the path on `[0, mΔ]`, hence on `[0, T]`.
  have hkey : ∀ (z : CoupledSample d) (s : ℝ≥0), s ≤ T →
      (EinsteinRelation.Probability.stoppedHistorySample Δ m z).1 s i -
          (EinsteinRelation.Probability.stoppedHistorySample Δ m z).1 0 i =
        z.1 s i - z.1 0 i := by
    intro z s hs
    rw [EinsteinRelation.Probability.stoppedHistorySample_path Δ m z s (hs.trans hT),
      EinsteinRelation.Probability.stoppedHistorySample_path Δ m z 0 zero_le]
  have hset : EinsteinRelation.Probability.stoppedHistorySample Δ m ⁻¹'
      {z : CoupledSample d | ∀ s : ℝ≥0, s ≤ T → -R < z.1 s i - z.1 0 i} =
      {z : CoupledSample d | ∀ s : ℝ≥0, s ≤ T → -R < z.1 s i - z.1 0 i} := by
    ext z
    simp only [Set.mem_preimage, Set.mem_setOf_eq]
    constructor
    · intro h s hs
      linarith [h s hs, hkey z s hs]
    · intro h s hs
      linarith [h s hs, hkey z s hs]
  have hpre := EinsteinRelation.Probability.measurable_stoppedHistorySample Δ m hprod
  rw [hset] at hpre
  exact hpre

end EinsteinRelation.Regeneration
