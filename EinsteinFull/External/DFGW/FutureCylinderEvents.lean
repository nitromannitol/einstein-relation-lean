import EinsteinFull.External.DFGW.FutureCylinder

/-! # Ordered future cylinder events

Finite intersections of state events at ordered times are represented by future cylinder
observables with indicator factors.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]

/-- The finite intersection of state events at the specified times. -/
def futureCylinderEvent (xs : List (ℝ≥0 × Set S)) : Set C(ℝ, S) :=
  {η | ∀ p ∈ xs, η p.1 ∈ p.2}

/-- Replace ordered absolute times by successive nonnegative time increments. -/
noncomputable def futureCylinderGaps : ℝ≥0 → List (ℝ≥0 × Set S) → List (ℝ≥0 × (S → ℝ))
  | _, [] => []
  | s, (t, A) :: xs => (t - s, A.indicator fun _ => 1) :: futureCylinderGaps t xs

omit [MeasurableSpace S] [BorelSpace S] in
/-- Successive gaps turn the indicator of an ordered finite intersection into a cylinder. -/
theorem futureCylinderGaps_apply (xs : List (ℝ≥0 × Set S))
    (hsorted : xs.Pairwise (fun p q => p.1 ≤ q.1))
    (s : ℝ≥0) (hs : ∀ p ∈ xs, s ≤ p.1) (η : C(ℝ, S)) :
    futureCylinder (futureCylinderGaps s xs) s η = (futureCylinderEvent xs).indicator (fun _ => 1) η := by
  classical
  induction xs generalizing s with
  | nil => simp [futureCylinderGaps, futureCylinder, futureCylinderEvent]
  | cons p xs ih =>
    obtain ⟨t, A⟩ := p
    have ht : s ≤ t := hs (t, A) (by simp)
    have htail : xs.Pairwise (fun p q => p.1 ≤ q.1) := (List.pairwise_cons.mp hsorted).2
    have hle : ∀ q ∈ xs, t ≤ q.1 := (List.pairwise_cons.mp hsorted).1
    have heq : ((t - s : ℝ≥0) : ℝ) + s = t := by
      exact_mod_cast (tsub_add_cancel_of_le ht)
    rw [futureCylinderGaps, futureCylinder, heq, ih htail t hle]
    have hev : η ∈ futureCylinderEvent ((t, A) :: xs) ↔
        η t ∈ A ∧ η ∈ futureCylinderEvent xs := by
      simp [futureCylinderEvent]
    by_cases hA : η t ∈ A <;> by_cases hx : η ∈ futureCylinderEvent xs <;>
      simp [hev, hA, hx]

omit [TopologicalSpace S] [BorelSpace S] in
/-- Measurable state events yield admissible indicator factors. -/
theorem futureCylinderGaps_admissible (s : ℝ≥0) (xs : List (ℝ≥0 × Set S))
    (hxs : ∀ p ∈ xs, MeasurableSet p.2) : FutureCylinderAdmissible (futureCylinderGaps s xs) := by
  classical
  induction xs generalizing s with
  | nil => simp [FutureCylinderAdmissible, futureCylinderGaps]
  | cons p xs ih =>
    obtain ⟨t, A⟩ := p
    have hA : MeasurableSet A := hxs (t, A) (by simp)
    have htail : ∀ p ∈ xs, MeasurableSet p.2 := fun p hp => hxs p (by simp [hp])
    intro q hq
    simp only [futureCylinderGaps, List.mem_cons] at hq
    rcases hq with rfl | hq
    · refine ⟨(measurable_const.indicator hA), ⟨1, fun x => ?_⟩⟩
      by_cases hx : x ∈ A <;> simp [hx]
    · exact ih t htail q hq

end EinsteinFull.External.DFGW
