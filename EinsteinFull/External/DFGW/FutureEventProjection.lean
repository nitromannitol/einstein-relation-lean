import EinsteinFull.External.DFGW.FutureCylinderEvents
import EinsteinFull.External.DFGW.StateProjectionClosure
import Mathlib.Data.List.Sort

/-! # Future cylinder event projections

Indicators of finite intersections of future state events have current-state-determined past
projections.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A finite intersection of measurable future state events is measurable. -/
theorem measurableSet_futureCylinderEvent (xs : List (ℝ≥0 × Set S))
    (hxs : ∀ p ∈ xs, MeasurableSet p.2) : MeasurableSet (futureCylinderEvent xs) := by
  induction xs with
  | nil => simp [futureCylinderEvent]
  | cons p xs ih =>
    obtain ⟨t, A⟩ := p
    have hA : MeasurableSet A := hxs (t, A) (by simp)
    have htail : ∀ p ∈ xs, MeasurableSet p.2 := fun p hp => hxs p (by simp [hp])
    have heq : futureCylinderEvent ((t, A) :: xs) =
        (fun η : C(ℝ, S) => η t) ⁻¹' A ∩ futureCylinderEvent xs := by
      ext η
      simp [futureCylinderEvent]
    rw [heq]
    exact (hA.preimage (continuous_eval_const _).measurable).inter (ih htail)

/-- Every finite future cylinder event has a state-determined past indicator projection. -/
theorem futureCylinderEvent_mem_stateDeterminedPast (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (xs : List (ℝ≥0 × Set S)) (hxs : ∀ p ∈ xs, MeasurableSet p.2)
    (hfinite : P (futureCylinderEvent xs) ≠ ⊤) :
    indicatorConstLp 2 (measurableSet_futureCylinderEvent xs hxs)
      hfinite (1 : ℝ) ∈ stateDeterminedPast P := by
  let : IsProbabilityMeasure P := hP.probability
  classical
  let leq : (ℝ≥0 × Set S) → (ℝ≥0 × Set S) → Bool := fun p q => decide (p.1 ≤ q.1)
  let ys := xs.mergeSort leq
  have hperm : ys.Perm xs := List.mergeSort_perm xs leq
  have hsorted : ys.Pairwise (fun p q => p.1 ≤ q.1) := by
    have h := List.pairwise_mergeSort (le := leq)
      (fun a b c hab hbc => by simpa only [leq, decide_eq_true_eq] using
        (le_trans (by simpa only [leq, decide_eq_true_eq] using hab)
          (by simpa only [leq, decide_eq_true_eq] using hbc) : a.1 ≤ c.1))
      (fun a b => by simp only [leq, Bool.or_eq_true, decide_eq_true_eq]; exact le_total a.1 b.1) xs
    simpa only [ys, leq, decide_eq_true_eq] using h
  have hys : ∀ p ∈ ys, MeasurableSet p.2 := fun p hp => hxs p (hperm.mem_iff.mp hp)
  have hevent : futureCylinderEvent ys = futureCylinderEvent xs := by
    ext η
    simp only [futureCylinderEvent, Set.mem_ofPred_eq]
    exact ⟨fun h p hp => h p (hperm.mem_iff.mpr hp),
      fun h p hp => h p (hperm.mem_iff.mp hp)⟩
  let cs := futureCylinderGaps 0 ys
  have hcs : FutureCylinderAdmissible cs := futureCylinderGaps_admissible 0 ys hys
  have hrepr : futureCylinder cs 0 = (futureCylinderEvent xs).indicator (fun _ => (1 : ℝ)) := by
    funext η
    have h := futureCylinderGaps_apply ys hsorted 0 (fun _ _ => bot_le) η
    simpa only [cs, NNReal.coe_zero, hevent] using h
  have hmem := futureCylinder_mem_stateDeterminedPast hP cs hcs
  have heq : (futureCylinder_memLp hP cs hcs 0).toLp (futureCylinder cs 0) =
      indicatorConstLp 2 (measurableSet_futureCylinderEvent xs hxs)
        hfinite (1 : ℝ) := by
    apply Lp.ext
    filter_upwards [MemLp.coeFn_toLp (futureCylinder_memLp hP cs hcs 0),
      indicatorConstLp_coeFn (p := 2) (hs := measurableSet_futureCylinderEvent xs hxs)
        (hμs := measure_ne_top P (futureCylinderEvent xs)) (c := (1 : ℝ))] with η h1 h2
    rw [h1, h2, hrepr]
  rw [heq] at hmem
  exact hmem

end EinsteinFull.External.DFGW
