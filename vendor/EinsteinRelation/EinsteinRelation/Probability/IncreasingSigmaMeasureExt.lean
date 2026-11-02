import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

open MeasureTheory
open MeasurableSpace
namespace EinsteinRelation.Probability

/-- Source `paper/main.tex:377–381`: finite measures agreeing on an exhausting increasing sequence of sigma-algebras agree everywhere. -/
theorem measure_eq_of_increasing_sigma {α : Type*} [mα : MeasurableSpace α]
    (μ ν : Measure α) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (m : ℕ → MeasurableSpace α) (hm : Monotone m) (hex : (⨆ n, m n) = mα)
    (heq : ∀ n s, @MeasurableSet α (m n) s → μ s = ν s) : μ = ν := by
  let C : Set (Set α) := {s | ∃ n, @MeasurableSet α (m n) s}
  have hC_pi : IsPiSystem C := by
    have h_each : ∀ n, IsPiSystem {s | @MeasurableSet α (m n) s} := by
      intro n
      exact @isPiSystem_measurableSet α (m n)
    have h_mono : Monotone fun n => {s | @MeasurableSet α (m n) s} := by
      intro n k hnk s hs
      have h_le : m n ≤ m k := hm hnk
      exact h_le s hs
    have hC_eq : C = ⋃ n, {s | @MeasurableSet α (m n) s} := by
      ext s; simp [C]
    rw [hC_eq]
    exact isPiSystem_iUnion_of_monotone (fun n => {s | @MeasurableSet α (m n) s}) h_each h_mono
  have hC_gen : generateFrom C = mα := by
    rw [← measurableSpace_iSup_eq m, hex]
  have hC_univ : μ Set.univ = ν Set.univ := by
    apply heq 0 Set.univ
    exact MeasurableSet.univ (m := m 0)
  refine ext_of_generate_finite C hC_gen.symm hC_pi (fun s hs => ?_) hC_univ
  rcases hs with ⟨n, hn⟩
  exact heq n s hn


end EinsteinRelation.Probability
