import EinsteinRelation.Regeneration.Construction
import EinsteinRelation.Probability.ContinuousFieldDecoder
import Mathlib.Topology.Metrizable.ContinuousMap
import Mathlib.Topology.UniformSpace.CompactConvergence

/-! # A measurable stopped version of the exact finite history

Source `paper/main.tex:272,353–364`. The stopped path keeps all values through
nDelta, and the bit record keeps exactly k<n. Measurability is proved in the
literal smaller history sigma, by countable evaluation decoding of continuous paths.
-/

open MeasureTheory EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinRelation.Probability

/-- Extend the actual finite history by a stopped path and zero later bits. -/
def stoppedHistorySample {d : ℕ} (Δ : ℝ≥0) (n : ℕ) (z : CoupledSample d) : CoupledSample d :=
  (⟨fun t => z.1 (min t ((n : ℝ≥0) * Δ)),
    z.1.continuous.comp (continuous_id.min continuous_const)⟩,
   fun k => if k < n then z.2 k else false)

/-- The stopped sample keeps the literal path on the closed past window. -/
theorem stoppedHistorySample_path {d : ℕ} (Δ : ℝ≥0) (n : ℕ) (z : CoupledSample d)
    (t : ℝ≥0) (ht : t ≤ (n : ℝ≥0) * Δ) :
    (stoppedHistorySample Δ n z).1 t = z.1 t := by
  change z.1 (min t ((n : ℝ≥0) * Δ)) = z.1 t
  rw [min_eq_left ht]

/-- Only the actual prior Bernoulli bits are retained. -/
theorem stoppedHistorySample_bit {d : ℕ} (Δ : ℝ≥0) (n : ℕ) (z : CoupledSample d)
    (k : ℕ) (hk : k < n) : (stoppedHistorySample Δ n z).2 k = z.2 k := by
  change (if k < n then z.2 k else false) = z.2 k
  rw [if_pos hk]

/-- The stopped extension is measurable from the exact finite-history sigma to the full sample. -/
theorem measurable_stoppedHistorySample {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    @Measurable (CoupledSample d) (CoupledSample d) (finiteHistorySigma Δ n)
      inferInstance (stoppedHistorySample Δ n) := by
  letI : MeasurableSpace (CoupledSample d) := finiteHistorySigma Δ n
  have heval : ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ →
      @Measurable (CoupledSample d) (Vec d) (finiteHistorySigma Δ n) inferInstance
        (fun z => z.1 t) := by
    intro t ht
    apply Measurable.of_comap_le
    exact le_sup_of_le_left (le_iSup_of_le ⟨t, zero_le, ht⟩ le_rfl)
  have hbit : ∀ k : ℕ, k < n →
      @Measurable (CoupledSample d) Bool (finiteHistorySigma Δ n) inferInstance
        (fun z => z.2 k) := by
    intro k hk
    apply Measurable.of_comap_le
    exact le_sup_of_le_right (le_iSup_of_le ⟨k, hk⟩ le_rfl)
  obtain ⟨D, hDm, hD⟩ := exists_measurable_continuousMap_decoder
    (X := ℝ≥0) (E := Vec d)
  have hraw : @Measurable (CoupledSample d) (ℝ≥0 → Vec d)
      (finiteHistorySigma Δ n) inferInstance
      (fun z => fun t => z.1 (min t ((n : ℝ≥0) * Δ))) :=
    Measurable.of_eval fun t => heval _ (min_le_right _ _)
  have hpath : @Measurable (CoupledSample d) (Path d) (finiteHistorySigma Δ n)
      inferInstance (fun z => (stoppedHistorySample Δ n z).1) := by
    have hm := hDm.comp hraw
    have heq : (fun z : CoupledSample d => D (fun t => z.1 (min t ((n : ℝ≥0) * Δ)))) =
        fun z => (stoppedHistorySample Δ n z).1 :=
      funext fun z => hD (stoppedHistorySample Δ n z).1
    change Measurable (fun z : CoupledSample d => D (fun t => z.1 (min t ((n : ℝ≥0) * Δ)))) at hm
    rw [heq] at hm
    exact hm
  have hbits : @Measurable (CoupledSample d) BernoulliSequence (finiteHistorySigma Δ n)
      inferInstance (fun z => (stoppedHistorySample Δ n z).2) := by
    refine Measurable.of_eval fun k => ?_
    by_cases hk : k < n
    · simpa only [stoppedHistorySample, if_pos hk] using hbit k hk
    · simp only [stoppedHistorySample, if_neg hk]
      exact measurable_const
  exact hpath.prodMk hbits

end EinsteinRelation.Probability
