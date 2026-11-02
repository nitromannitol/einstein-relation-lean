import EinsteinRelation.Regeneration.LastBit
import EinsteinRelation.Regeneration.NoBacktracking
import EinsteinRelation.Regeneration.Measurability

/-! # The literal forced-last-bit regeneration slice

Source `paper/main.tex:353–364`: an internal explicit Γ_m event obtained by
forcing bit m to one. This file proves its global measurability and the actual
regeneration slice identity. Exact finite-history measurability is a separate
internal obligation; no renewal or independence is assumed here.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

/-- Set only the last selected Bernoulli bit to one, leaving the path untouched. -/
def forceSampleBit {d : ℕ} (m : ℕ) (z : CoupledSample d) : CoupledSample d :=
  (z.1, Function.update z.2 m true)

/-- The explicit prestart event, with the prospective last bit forced to one. -/
def forcedBitTrialEvent {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ) :
    Set (CoupledSample d) :=
  {z | ∃ n, trialStartSequence Δ lam R (forceSampleBit m z) i n =
    (((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0)}

/-- Setting one bit is measurable on the actual sample space. -/
theorem measurable_forceSampleBit {d : ℕ} (m : ℕ) :
    Measurable (forceSampleBit (d := d) m) :=
  measurable_fst.prodMk (measurable_update_left.comp measurable_snd)

/-- For a sample whose selected bit is already one, forcing it does nothing. -/
theorem forceSampleBit_eq_self {d : ℕ} (m : ℕ) (z : CoupledSample d)
    (hb : z.2 m = true) : forceSampleBit m z = z := by
  change (z.1, Function.update z.2 m true) = (z.1, z.2)
  congr 1
  exact Function.update_eq_self_iff.mpr hb.symm

/-- The explicit event is globally measurable before the finer history proof. -/
theorem measurableSet_forcedBitTrialEvent {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (i : Fin d) (m : ℕ) : MeasurableSet (forcedBitTrialEvent Δ lam R i m) := by
  change MeasurableSet {z | ∃ n : ℕ, trialStartSequence Δ lam R (forceSampleBit m z) i n =
    (((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0)}
  simp only [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro n
  exact measurableSet_eq_fun
    ((measurable_trialStartSequence Δ lam R i n).comp (measurable_forceSampleBit m))
    measurable_const

/-- The actual finite-grid regeneration slice splits into past, last bit and future D. -/
theorem firstRegenerationTime_eq_iff_forcedBitTrialEvent {d : ℕ} (Δ : ℝ≥0)
    (hΔ : 0 < Δ) (lam R : ℝ) (z : CoupledSample d) (i : Fin d) (m : ℕ) :
    firstRegenerationTime Δ lam R z i =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ↔
    z ∈ forcedBitTrialEvent Δ lam R i m ∧ z.2 m = true ∧
      NoBacktracking R (pathTimeShift z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ)) i := by
  let T : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0) * Δ
  constructor
  · intro ht
    have hb := firstRegenerationTime_last_bit Δ hΔ lam R z i m ht
    obtain ⟨n, hn, hf⟩ := (firstRegenerationTime_eq_iff_trial Δ hΔ lam R z i T).mp ht
    refine ⟨?_, hb, ?_⟩
    · exact ⟨n, by rw [forceSampleBit_eq_self m z hb]; exact hn⟩
    · have hS : trialStartSequence Δ lam R z i n ≠ ⊤ :=
        hn ▸ ENNReal.coe_ne_top
      have hD := (trialFailureTime_eq_top_iff_noBacktracking Δ R z i _ hS).mp hf
      rw [hn, ENNReal.toNNReal_coe] at hD
      exact hD
  · rintro ⟨⟨n, hn⟩, hb, hD⟩
    rw [forceSampleBit_eq_self m z hb] at hn
    apply (firstRegenerationTime_eq_iff_trial Δ hΔ lam R z i T).mpr
    refine ⟨n, hn, ?_⟩
    have hS : trialStartSequence Δ lam R z i n ≠ ⊤ := hn ▸ ENNReal.coe_ne_top
    apply (trialFailureTime_eq_top_iff_noBacktracking Δ R z i _ hS).mpr
    rw [hn, ENNReal.toNNReal_coe]
    exact hD

end EinsteinRelation.Regeneration
