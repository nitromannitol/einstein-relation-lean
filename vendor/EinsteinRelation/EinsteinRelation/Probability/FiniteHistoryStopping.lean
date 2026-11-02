import EinsteinRelation.Probability.FiniteHistoryMeasurability
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Exact finite-history tests ignore the stopped extension

Source `paper/main.tex:353–364,383–397`. The exact history sigma-algebra is
the pullback under its stopped extension. Consequently every measurable
past test has the same value before and after that extension.
-/

open MeasureTheory EinsteinRelation.Regeneration
open scoped NNReal

namespace EinsteinRelation.Probability

/-- Stopping the same exact history twice has no further effect. -/
theorem stoppedHistorySample_idempotent {d : ℕ} (Δ : ℝ≥0) (n : ℕ) (z : CoupledSample d) :
    stoppedHistorySample Δ n (stoppedHistorySample Δ n z) = stoppedHistorySample Δ n z := by
  apply Prod.ext
  · apply ContinuousMap.ext
    intro t
    change z.1 (min (min t _) _) = z.1 (min t _)
    rw [min_assoc, min_self]
  · funext k
    by_cases hk : k < n <;> simp [stoppedHistorySample, hk]

/-- The exact finite past is precisely the information retained by the
stopped path and the bits with index strictly less than `n`. -/
theorem finiteHistorySigma_eq_comap_stopped {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    finiteHistorySigma (d := d) Δ n =
      MeasurableSpace.comap (stoppedHistorySample Δ n)
        (inferInstance : MeasurableSpace (CoupledSample d)) := by
  apply le_antisymm
  · unfold finiteHistorySigma
    apply sup_le
    · apply iSup_le
      intro t
      have hfun : (fun z : CoupledSample d => z.1 t) =
          (fun z : CoupledSample d => z.1 t) ∘ stoppedHistorySample Δ n := by
        funext z
        exact (stoppedHistorySample_path Δ n z t t.2.2).symm
      rw [hfun, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono
        (((continuous_eval_const (t : ℝ≥0)).measurable.comp measurable_fst).comap_le)
    · apply iSup_le
      intro k
      have hfun : (fun z : CoupledSample d => z.2 k) =
          (fun z : CoupledSample d => z.2 k) ∘ stoppedHistorySample Δ n := by
        funext z
        exact (stoppedHistorySample_bit Δ n z k k.2).symm
      rw [hfun, ← MeasurableSpace.comap_comp]
      exact MeasurableSpace.comap_mono
        (((measurable_pi_apply (X := fun _ : ℕ => Bool) (k : ℕ)).comp measurable_snd).comap_le)
  · exact (measurable_stoppedHistorySample Δ n).comap_le

/-- Every exact-past measurable test has the same value on the stopped
extension, including real tests used in deterministic restart. -/
theorem finiteHistory_test_stopped {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    {E : Type*} [MeasurableSpace E] [MeasurableSingletonClass E]
    (F : CoupledSample d → E)
    (hF : @Measurable (CoupledSample d) E (finiteHistorySigma Δ n) inferInstance F)
    (z : CoupledSample d) : F (stoppedHistorySample Δ n z) = F z := by
  rw [finiteHistorySigma_eq_comap_stopped] at hF
  exact hF.factorsThrough (stoppedHistorySample_idempotent Δ n z)


end EinsteinRelation.Probability
