import EinsteinRelation.Probability.FiniteHistoryStopping
import EinsteinRelation.Regeneration.Coupling
import Mathlib.MeasureTheory.Function.FactorsThrough

/-!
# Splitting an exact finite history at its last grid interval

Source `paper/main.tex:377–381`. The path through `(n+1)Δ` and the bits
before `n+1` are measurable functions of the exact history through `nΔ`
and the first history of the deterministically shifted sample. This
gives bounded joint tests for iterating one-interval identities.
-/

open MeasureTheory EinsteinRelation.Regeneration
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Probability

/-- The pair of actual histories on either side of the last grid interval. -/
def splitHistory {d : ℕ} (Δ : ℝ≥0) (n : ℕ) (z : CoupledSample d) :
    CoupledSample d × CoupledSample d :=
  (stoppedHistorySample Δ n z,
    stoppedHistorySample Δ 1 (sampleTimeShift Δ z ((n : ℝ≥0) * Δ)))

/-- The two stopped histories retain the entire exact next history. -/
theorem finiteHistorySigma_le_comap_splitHistory {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ) :
    finiteHistorySigma (d := d) Δ (n + 1) ≤
      MeasurableSpace.comap (splitHistory Δ n)
        (inferInstance : MeasurableSpace (CoupledSample d × CoupledSample d)) := by
  let mS : MeasurableSpace (CoupledSample d) := inferInstance
  let m := MeasurableSpace.comap (splitHistory (d := d) Δ n) (mS.prod mS)
  have hs : @Measurable (CoupledSample d) (CoupledSample d × CoupledSample d)
      m (mS.prod mS) (splitHistory Δ n) := fun s hs => ⟨s, hs, rfl⟩
  letI : MeasurableSpace (CoupledSample d) := mS
  unfold finiteHistorySigma
  apply sup_le
  · apply iSup_le
    intro t
    have ht : (t : ℝ≥0) ≤ ((n + 1 : ℕ) : ℝ≥0) * Δ := t.property.2
    suffices @Measurable (CoupledSample d) (Vec d) m inferInstance
        (fun z => z.1 (t : ℝ≥0)) from this.comap_le
    by_cases htn : (t : ℝ≥0) ≤ (n : ℝ≥0) * Δ
    · have h := ((continuous_eval_const (t : ℝ≥0)).measurable.comp hs.fst.fst)
      simpa [splitHistory, stoppedHistorySample, Function.comp_def, min_eq_left htn] using h
    · have hrem : (t : ℝ≥0) - (n : ℝ≥0) * Δ ≤ Δ := by
        rw [tsub_le_iff_right]
        simpa only [Nat.cast_add, Nat.cast_one, add_mul, one_mul, add_comm] using ht
      have hadd : (n : ℝ≥0) * Δ + ((t : ℝ≥0) - (n : ℝ≥0) * Δ) = t :=
        add_tsub_cancel_of_le (not_le.mp htn).le
      have heval : (fun z : CoupledSample d =>
          (splitHistory Δ n z).2.1 ((t : ℝ≥0) - (n : ℝ≥0) * Δ)) =
          fun z => z.1 (t : ℝ≥0) := by
        funext z
        simp [splitHistory, stoppedHistorySample, sampleTimeShift, pathTimeShift,
          min_eq_left hrem, hadd]
      rw [← heval]
      exact (continuous_eval_const _).measurable.comp hs.snd.fst
  · apply iSup_le
    intro k
    suffices @Measurable (CoupledSample d) Bool m inferInstance
        (fun z => z.2 (k : ℕ)) from this.comap_le
    by_cases hkn : (k : ℕ) < n
    · have h := (measurable_pi_apply (X := fun _ : ℕ => Bool) (k : ℕ)).comp hs.fst.snd
      simpa only [splitHistory, stoppedHistorySample, Function.comp_def, if_pos hkn] using h
    · have hkeq : (k : ℕ) = n := by omega
      have h := (measurable_pi_apply (X := fun _ : ℕ => Bool) 0).comp hs.snd.snd
      simpa only [splitHistory, stoppedHistorySample, Nat.zero_lt_one, if_pos,
        sampleTimeShift, gridIndex_mul Δ hΔ n, Nat.add_zero, hkeq, Function.comp_def] using h

/-- Every bounded next-history test is a bounded measurable joint test
of the exact past and the last stopped interval. The extension away
from actual history pairs is clipped to the original bound. -/
theorem exists_bounded_splitHistory_factor {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ) (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ (n + 1)) inferInstance F)
    (hb : BoundedRealTest F) :
    ∃ G : CoupledSample d × CoupledSample d → ℝ,
      Measurable G ∧ BoundedRealTest G ∧ ∀ z, F z = G (splitHistory Δ n z) := by
  have hm := hF.mono (finiteHistorySigma_le_comap_splitHistory Δ hΔ n) le_rfl
  obtain ⟨G, hG, heq⟩ := hm.exists_eq_measurable_comp
  obtain ⟨C, hC⟩ := hb
  have hC0 : 0 ≤ C := (abs_nonneg (F (0, fun _ => false))).trans (hC _)
  refine ⟨fun p => max (-C) (min (G p) C),
    measurable_const.max (hG.min measurable_const), ⟨C, fun p => ?_⟩, ?_⟩
  · exact abs_le.mpr ⟨le_max_left _ _, max_le (by linarith) (min_le_right _ _)⟩
  · intro z
    have hz := congrFun heq z
    dsimp only [Function.comp_def] at hz
    have hbound := abs_le.mp (hC z)
    change F z = max (-C) (min (G (splitHistory Δ n z)) C)
    rw [← hz, min_eq_left hbound.2, max_eq_right hbound.1]


end EinsteinRelation.Probability
