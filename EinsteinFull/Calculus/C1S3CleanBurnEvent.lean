import EinsteinRelation.Regeneration.ForcedBitSlice

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration

/-- A Burn-selected prospective trial, with only its current shifted coin
forced. This retains the literal original prefix and trial indices. -/
def c1S3TrialBurnPrebridge {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ)
    (m : ℕ) (i : Fin d) (J N k : ℕ) : Set (Regeneration.CoupledSample d) :=
  {z |
    let w := Regeneration.forceSampleBit k
      (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ))
    let S := Regeneration.trialStartSequence Δ lam R w i J
    Regeneration.trialStartSequence Δ lam R w i (J + N) =
      ((((k + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
    S ≠ ⊤ ∧ z.1 0 i + Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ) ≤
      z.1 ((m : ℝ≥0) * Δ + (S.toNNReal - Δ)) i + R}

/-- The Burn prebridge has its ordinary measurable representation before
passing to the smaller, pre-coin finite-history sigma algebra. -/
theorem c1_s3_measurableSet_trial_burn_prebridge {d : ℕ}
    (Δ : ℝ≥0) (lam R : ℝ) (m : ℕ) (i : Fin d) (J N k : ℕ) :
    MeasurableSet (c1S3TrialBurnPrebridge Δ lam R m i J N k) := by
  have hw : Measurable (fun z : Regeneration.CoupledSample d =>
      Regeneration.forceSampleBit k (Regeneration.sampleTimeShift Δ z ((m : ℝ≥0) * Δ))) :=
    (Regeneration.measurable_forceSampleBit k).comp
      ((Regeneration.measurable_sampleTimeShift Δ).comp (measurable_const.prodMk measurable_id))
  have hS := (Regeneration.measurable_trialStartSequence Δ lam R i J).comp hw
  have heval : Continuous (fun p : ℝ≥0 × Path d => p.2 p.1 i) :=
    (continuous_apply i).comp (continuous_snd.eval continuous_fst)
  have hzero : Measurable (fun z : Regeneration.CoupledSample d => z.1 0 i) :=
    heval.measurable.comp (measurable_const.prodMk measurable_fst)
  have hmax : Measurable (fun z : Regeneration.CoupledSample d =>
      Regeneration.coordinateMaximum z.1 i ((m : ℝ≥0) * Δ)) :=
    (Regeneration.measurable_coordinateMaximum i).comp (measurable_const.prodMk measurable_fst)
  have ht : Measurable (fun z : Regeneration.CoupledSample d =>
      (m : ℝ≥0) * Δ + ((Regeneration.trialStartSequence Δ lam R
        (Regeneration.forceSampleBit k (Regeneration.sampleTimeShift Δ z
          ((m : ℝ≥0) * Δ))) i J).toNNReal - Δ)) :=
    measurable_const.add (hS.ennreal_toNNReal.sub_const Δ)
  exact (measurableSet_eq_fun
    ((Regeneration.measurable_trialStartSequence Δ lam R i (J + N)).comp hw)
    measurable_const).inter ((measurableSet_eq_fun hS measurable_const).compl.inter
      (measurableSet_le (hzero.add hmax)
        ((heval.measurable.comp (ht.prodMk measurable_fst)).add_const R)))

end EinsteinFull.Blueprint
