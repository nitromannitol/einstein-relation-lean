import EinsteinRelation.Regeneration.TrialPrefix
import EinsteinRelation.Regeneration.ForcedBitSlice
import EinsteinRelation.Regeneration.FreshEventMass
import EinsteinRelation.Probability.StoppedHistory

/-! # The prestart event belongs to the exact finite history

Source `paper/main.tex:353–364`. Forcing bit `m` makes the trial-selection event
at `(m+1)Δ` depend only on the path through `mΔ` and the bits strictly before
`m`. The stopped-history extension gives a measurable representation in that
smaller sigma-algebra. Consequently the actual event has the fresh-bit mass
identity supplied by the coupled kernel.
-/

open MeasureTheory
open scoped NNReal ENNReal
open EinsteinRelation.Probability
  (stoppedHistorySample stoppedHistorySample_path stoppedHistorySample_bit
    measurable_stoppedHistorySample)

namespace EinsteinRelation.Regeneration

/-- Stopping the history at `mΔ` preserves the literal prestart event
(`paper/main.tex:353–364`). -/
theorem mem_forcedBitTrialEvent_stoppedHistory_iff {d : ℕ} (Δ : ℝ≥0)
    (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ)
    (z : CoupledSample d) :
    z ∈ forcedBitTrialEvent Δ lam R i m ↔
      stoppedHistorySample Δ m z ∈ forcedBitTrialEvent Δ lam R i m := by
  have hpre : ∀ t ∈ Set.Icc (0 : ℝ≥0) ((m : ℝ≥0) * Δ),
      (forceSampleBit m z).1 t =
        (forceSampleBit m (stoppedHistorySample Δ m z)).1 t := by
    intro t ht
    exact (stoppedHistorySample_path Δ m z t ht.2).symm
  have hbits : ∀ k : ℕ, (k : ℝ≥0) * Δ ≤ (m : ℝ≥0) * Δ →
      (forceSampleBit m z).2 k =
        (forceSampleBit m (stoppedHistorySample Δ m z)).2 k := by
    intro k hk
    have hkm : k ≤ m := by
      exact_mod_cast (mul_le_mul_iff_left₀ hΔ).mp hk
    by_cases heq : k = m
    · subst k
      simp only [forceSampleBit, Function.update_self]
    · have hlt : k < m := lt_of_le_of_ne hkm heq
      simp only [forceSampleBit, Function.update_of_ne heq,
        stoppedHistorySample_bit Δ m z k hlt]
  have htime : (((m + 1 : ℕ) : ℝ≥0) * Δ) = (m : ℝ≥0) * Δ + Δ := by
    rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have heq := trialStartSequence_eq_of_prefix Δ hΔ lam R hR
      (forceSampleBit m z) (forceSampleBit m (stoppedHistorySample Δ m z)) i n
      ((m : ℝ≥0) * Δ) hpre hbits (by rw [hn, htime])
    exact heq.symm.trans hn
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have heq := trialStartSequence_eq_of_prefix Δ hΔ lam R hR
      (forceSampleBit m (stoppedHistorySample Δ m z)) (forceSampleBit m z) i n
      ((m : ℝ≥0) * Δ) (fun t ht => (hpre t ht).symm)
      (fun k hk => (hbits k hk).symm) (by rw [hn, htime])
    exact heq.symm.trans hn

/-- The explicit `Γ_m` event is measurable for the exact past sigma-algebra,
whose Bernoulli generators have indices strictly below `m`
(`paper/main.tex:353–364`). -/
theorem measurableSet_forcedBitTrialEvent_finiteHistory {d : ℕ} (Δ : ℝ≥0)
    (hΔ : 0 < Δ) (lam R : ℝ) (hR : 0 < R) (i : Fin d) (m : ℕ) :
    @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ m)
      (forcedBitTrialEvent Δ lam R i m) := by
  have hset : forcedBitTrialEvent Δ lam R i m =
      stoppedHistorySample Δ m ⁻¹' forcedBitTrialEvent Δ lam R i m := by
    ext z
    exact mem_forcedBitTrialEvent_stoppedHistory_iff Δ hΔ lam R hR i m z
  rw [hset]
  exact measurable_stoppedHistorySample Δ m
    (measurableSet_forcedBitTrialEvent Δ lam R i m)

/-- The actual prestart event, together with the successful last bit, has mass
`δ` times its prestart mass (`paper/main.tex:353–364`). -/
theorem measure_annealed_forcedBitTrialEvent_lastBit {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hFresh : HasFreshBits Q Δ δ K) (lam R : ℝ) (hR : 0 < R)
    (i : Fin d) (m : ℕ) :
    annealedCoupledLaw Q K
      {ωz | ωz.2 ∈ forcedBitTrialEvent Δ lam R i m ∧ ωz.2.2 m = true} =
      ENNReal.ofReal δ * annealedCoupledLaw Q K
        {ωz | ωz.2 ∈ forcedBitTrialEvent Δ lam R i m} :=
  measure_annealed_fresh_bit Q K hK Δ δ hδ hFresh m _
    (measurableSet_forcedBitTrialEvent_finiteHistory Δ hΔ lam R hR i m)


end EinsteinRelation.Regeneration
