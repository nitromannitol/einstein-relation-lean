import EinsteinFull.Regeneration.LaterMaximumMeasurability
import EinsteinRelation.Regeneration.RenewalRecordIteration
import EinsteinRelation.Regeneration.CycleRewardFactorsDecoder
import EinsteinRelation.Regeneration.RegenerationShiftObservables

/-!
# Cycle observables read from the regeneration records

The duration, the coordinate displacements and the absolute coordinate maxima of a later
regeneration cycle are measurable functions of the future record at the start of the cycle:
the regeneration times use the path only through its increments, and the record holds the path
after the regeneration time, translated to start at the origin.
-/

open MeasureTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

variable {d : ℕ}

/-- The first regeneration time of a record, as a real duration. -/
noncomputable def recordDuration (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (y : FutureState d i R) : ℝ :=
  ((firstRegenerationTime Δ lam R (recordSample y) i).toNNReal : ℝ)

/-- The displacement in coordinate `j` of a record at its first regeneration time. -/
noncomputable def recordDisplacement (Δ : ℝ≥0) (lam R : ℝ) (i j : Fin d)
    (y : FutureState d i R) : ℝ :=
  y.1 (firstRegenerationTime Δ lam R (recordSample y) i).toNNReal j - y.1 0 j

/-- The absolute coordinate maximum of a record up to its first regeneration time. -/
noncomputable def recordMaximum (Δ : ℝ≥0) (lam R : ℝ) (i j : Fin d)
    (y : FutureState d i R) : ℝ :=
  absoluteCoordinateMaximum j (firstRegenerationTime Δ lam R (recordSample y) i).toNNReal y.1

theorem measurable_recordFirstTime (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) :
    Measurable fun y : FutureState d i R =>
      (firstRegenerationTime Δ lam R (recordSample y) i).toNNReal :=
  ((measurable_firstRegenerationTime Δ lam R i).comp
    (measurable_recordSample i R)).ennreal_toNNReal

theorem measurable_recordDuration (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) :
    Measurable (recordDuration Δ lam R i) :=
  measurable_coe_nnreal_real.comp (measurable_recordFirstTime Δ lam R i)

theorem measurable_recordDisplacement (Δ : ℝ≥0) (lam R : ℝ) (i j : Fin d) :
    Measurable (recordDisplacement Δ lam R i j) := by
  have hx := measurable_path_eval.comp ((measurable_recordFirstTime Δ lam R i).prodMk
    (measurable_fst : Measurable (Prod.fst : FutureState d i R → Path d)))
  have hx0 : Measurable (fun y : FutureState d i R => y.1 0 j) :=
    (measurable_pi_apply j).comp ((continuous_eval_const (0 : ℝ≥0)).measurable.comp measurable_fst)
  exact ((measurable_pi_apply j).comp hx).sub hx0

theorem measurable_recordMaximum (Δ : ℝ≥0) (lam R : ℝ) (i j : Fin d) :
    Measurable (recordMaximum Δ lam R i j) :=
  (continuous_absoluteCoordinateMaximum j).measurable.comp
    ((measurable_recordFirstTime Δ lam R i).prodMk measurable_fst)

/-- The first regeneration time of the record at a finite regeneration time is the next cycle
duration. -/
theorem firstRegenerationTime_iteratedRecord (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (k : ℕ)
    (q : FieldPair d × CoupledSample d) :
    firstRegenerationTime Δ lam R (recordSample (iteratedRecord Δ lam R i k q)) i =
      firstRegenerationTime Δ lam R
        (sampleTimeShift Δ q.2 (regenerationTime Δ lam R q.2 i k).toNNReal) i := by
  have hs : recordSample (iteratedRecord Δ lam R i k q) =
      recenterSample (q.2.1 (regenerationTime Δ lam R q.2 i k).toNNReal)
        (sampleTimeShift Δ q.2 (regenerationTime Δ lam R q.2 i k).toNNReal) := rfl
  rw [hs, firstRegenerationTime_recenterSample]

/-- On a sample with finite regeneration times, the duration of the later cycle `n` is the
first regeneration time of the record at the regeneration time `n + 1`. -/
theorem laterDuration_eq_recordDuration (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (n : ℕ)
    (q : FieldPair d × CoupledSample d)
    (hfin : ∀ k, regenerationTime Δ lam R q.2 i k ≠ ⊤) :
    laterDuration Δ lam R i n q =
      recordDuration Δ lam R i (iteratedRecord Δ lam R i (n + 1) q) := by
  have hsucc : regenerationTime Δ lam R q.2 i (n + 2) = regenerationTime Δ lam R q.2 i (n + 1) +
      firstRegenerationTime Δ lam R
        (sampleTimeShift Δ q.2 (regenerationTime Δ lam R q.2 i (n + 1)).toNNReal) i :=
    regenerationTime_succ_eq Δ lam R q.2 i (n + 1) (hfin (n + 1))
  have hf : firstRegenerationTime Δ lam R
      (sampleTimeShift Δ q.2 (regenerationTime Δ lam R q.2 i (n + 1)).toNNReal) i ≠ ⊤ := by
    intro h
    exact hfin (n + 2) (by rw [hsucc, h, add_top])
  unfold laterDuration laterCycleDuration regenerationClock recordDuration
  rw [firstRegenerationTime_iteratedRecord, hsucc, ENNReal.toReal_add (hfin (n + 1)) hf]
  simp only [ENNReal.coe_toNNReal_eq_toReal, add_sub_cancel_left]

/-- On a sample with finite regeneration times, the coordinate displacement of the later cycle
`n` is the displacement of the record at the regeneration time `n + 1`. -/
theorem laterCoordinateReward_eq_recordDisplacement (Δ : ℝ≥0) (lam R : ℝ) (i j : Fin d)
    (n : ℕ) (q : FieldPair d × CoupledSample d)
    (hfin : ∀ k, regenerationTime Δ lam R q.2 i k ≠ ⊤) :
    laterCoordinateReward Δ lam R i j n q =
      recordDisplacement Δ lam R i j (iteratedRecord Δ lam R i (n + 1) q) := by
  have hsucc : regenerationTime Δ lam R q.2 i (n + 2) = regenerationTime Δ lam R q.2 i (n + 1) +
      firstRegenerationTime Δ lam R
        (sampleTimeShift Δ q.2 (regenerationTime Δ lam R q.2 i (n + 1)).toNNReal) i :=
    regenerationTime_succ_eq Δ lam R q.2 i (n + 1) (hfin (n + 1))
  have hf : firstRegenerationTime Δ lam R
      (sampleTimeShift Δ q.2 (regenerationTime Δ lam R q.2 i (n + 1)).toNNReal) i ≠ ⊤ := by
    intro h
    exact hfin (n + 2) (by rw [hsucc, h, add_top])
  unfold laterCoordinateReward recordDisplacement
  rw [firstRegenerationTime_iteratedRecord, hsucc, ENNReal.toNNReal_add (hfin (n + 1)) hf]
  simp [iteratedRecord, futureRecord]

/-- On a sample with finite regeneration times, the absolute coordinate maximum of the later
cycle `n` is the maximum of the record at the regeneration time `n + 1`. -/
theorem laterCoordinateMaximum_eq_recordMaximum (Δ : ℝ≥0) (lam R : ℝ) (i j : Fin d)
    (n : ℕ) (q : FieldPair d × CoupledSample d)
    (hfin : ∀ k, regenerationTime Δ lam R q.2 i k ≠ ⊤) :
    laterCoordinateMaximum Δ lam R i j n q =
      recordMaximum Δ lam R i j (iteratedRecord Δ lam R i (n + 1) q) := by
  have hsucc : regenerationTime Δ lam R q.2 i (n + 2) = regenerationTime Δ lam R q.2 i (n + 1) +
      firstRegenerationTime Δ lam R
        (sampleTimeShift Δ q.2 (regenerationTime Δ lam R q.2 i (n + 1)).toNNReal) i :=
    regenerationTime_succ_eq Δ lam R q.2 i (n + 1) (hfin (n + 1))
  have hf : firstRegenerationTime Δ lam R
      (sampleTimeShift Δ q.2 (regenerationTime Δ lam R q.2 i (n + 1)).toNNReal) i ≠ ⊤ := by
    intro h
    exact hfin (n + 2) (by rw [hsucc, h, add_top])
  unfold laterCoordinateMaximum recordMaximum absoluteCoordinateMaximum
  rw [firstRegenerationTime_iteratedRecord, hsucc,
    ENNReal.toNNReal_add (hfin (n + 1)) hf, add_tsub_cancel_left]
  simp [iteratedRecord, futureRecord]

/-- If every later record has the law of the first record under `ν`, and the first regeneration
time is finite under `μ` and under `ν`, then all regeneration times are finite under `μ`. -/
theorem ae_regenerationTime_ne_top_of_record_laws (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d)
    (μ ν : Measure (FieldPair d × CoupledSample d))
    (hμ : ∀ k, 1 ≤ k → μ.map (iteratedRecord Δ lam R i k) = ν.map (iteratedRecord Δ lam R i 0))
    (h1μ : ∀ᵐ q ∂μ, firstRegenerationTime Δ lam R q.2 i ≠ ⊤)
    (h1ν : ∀ᵐ q ∂ν, firstRegenerationTime Δ lam R q.2 i ≠ ⊤) :
    ∀ᵐ q ∂μ, ∀ k, regenerationTime Δ lam R q.2 i k ≠ ⊤ := by
  have hf0 : ∀ q : FieldPair d × CoupledSample d,
      firstRegenerationTime Δ lam R (recordSample (iteratedRecord Δ lam R i 0 q)) i =
        firstRegenerationTime Δ lam R q.2 i := by
    intro q
    rw [firstRegenerationTime_iteratedRecord]
    simp [regenerationTime, sampleTimeShift_zero]
  have hS : MeasurableSet {y : FutureState d i R |
      firstRegenerationTime Δ lam R (recordSample y) i = ⊤} :=
    ((measurable_firstRegenerationTime Δ lam R i).comp (measurable_recordSample i R))
      (measurableSet_singleton ⊤)
  have hrec : ∀ k, ∀ᵐ q ∂μ,
      firstRegenerationTime Δ lam R (recordSample (iteratedRecord Δ lam R i k q)) i ≠ ⊤ := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · filter_upwards [h1μ] with q hq
      rwa [hf0]
    · have hν0 : ν {q | firstRegenerationTime Δ lam R
          (recordSample (iteratedRecord Δ lam R i 0 q)) i = ⊤} = 0 := by
        have h0 := ae_iff.mp h1ν
        simpa only [hf0, ne_eq, not_not] using h0
      have h := congrArg (fun m : Measure (FutureState d i R) =>
        m {y | firstRegenerationTime Δ lam R (recordSample y) i = ⊤}) (hμ k hk)
      simp only [Measure.map_apply (measurable_iteratedRecord Δ lam R i k) hS,
        Measure.map_apply (measurable_iteratedRecord Δ lam R i 0) hS] at h
      have h' : μ {q | firstRegenerationTime Δ lam R
          (recordSample (iteratedRecord Δ lam R i k q)) i = ⊤} =
          ν {q | firstRegenerationTime Δ lam R
            (recordSample (iteratedRecord Δ lam R i 0 q)) i = ⊤} := h
      rw [ae_iff]
      simp only [ne_eq, not_not]
      rw [h', hν0]
  rw [ae_all_iff]
  intro k
  induction k with
  | zero => exact Filter.Eventually.of_forall fun q => by simp [regenerationTime]
  | succ k ih =>
    filter_upwards [ih, hrec k] with q hq hf
    rw [regenerationTime_succ_eq Δ lam R q.2 i k hq, ← firstRegenerationTime_iteratedRecord Δ lam R i k q]
    exact ENNReal.add_ne_top.mpr ⟨hq, hf⟩

end EinsteinFull.Regeneration
