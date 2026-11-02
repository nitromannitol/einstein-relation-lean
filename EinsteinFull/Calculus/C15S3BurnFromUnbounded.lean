import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinRelation.Regeneration.TrialGeometry

open EinsteinRelation Regeneration MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

theorem c15_s3_burn_of_unbounded_excursions
    {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ) (hlam : 0 < lam) (hR : 0 < R)
    (m : ℕ) (i : Fin d) (q : FieldPair d × CoupledSample d)
    (hunbounded : ∀ B : ℝ, ∃ t : ℝ≥0, B ≤ q.2.1 t i - q.2.1 0 i)
    (hfinite : ∀ n, trialStartSequence Δ lam R
      (sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) i n ≠ ⊤) :
    ∃ J, q ∈ couplingScopeTrialBurn Δ lam R m i J := by
  let a : ℝ≥0 := (m : ℝ≥0) * Δ
  let w := sampleTimeShift Δ q.2 a
  obtain ⟨t, ht⟩ := hunbounded (coordinateMaximum q.2.1 i a + 1)
  have hat : a ≤ t := by
    by_contra h
    have hb := displacement_le_coordinateMaximum q.2.1 i t a (le_of_not_ge h)
    linarith
  have htend := coupling_scope_trial_prebridge_tendsto_atTop Δ hΔ lam R hlam hR w i hfinite
  obtain ⟨J, hJ⟩ := (Filter.eventually_atTop.1 (htend.eventually (Filter.eventually_ge_atTop (t - a))))
  have htime : t - a ≤ (trialStartSequence Δ lam R w i J).toNNReal - Δ := hJ J le_rfl
  have hmax := displacement_le_coordinateMaximum w.1 i (t - a)
    ((trialStartSequence Δ lam R w i J).toNNReal - Δ) htime
  have hslack := trial_prestart_maximum_slack Δ hΔ lam R hlam hR w i J (hfinite J)
  have hshift : a + (t - a) = t := add_tsub_cancel_of_le hat
  change q.2.1 (a + (t - a)) i - q.2.1 (a + 0) i ≤ _ at hmax
  rw [hshift, add_zero] at hmax
  change coordinateMaximum w.1 i _ ≤ q.2.1 (a + _) i - q.2.1 (a + 0) i + R at hslack
  rw [add_zero] at hslack
  refine ⟨J, ?_⟩
  change trialStartSequence Δ lam R w i J ≠ ⊤ ∧
    q.2.1 0 i + coordinateMaximum q.2.1 i a ≤
      q.2.1 (a + ((trialStartSequence Δ lam R w i J).toNNReal - Δ)) i + R
  exact ⟨hfinite J, by linarith⟩

end EinsteinFull.Blueprint
