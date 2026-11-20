import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Measure.Real

/-! # Convergence in measure in finite products

Coordinatewise convergence in measure to zero implies convergence in measure in a finite
product of normed spaces.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.External.DFGW

variable {Ω ι J : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
variable [Fintype J] {l : Filter ι}

/-- A finite vector of real random variables converges to zero in measure if each coordinate
does. -/
theorem tendstoInMeasure_pi_zero (F : ι → Ω → J → ℝ)
    (hF : ∀ j, TendstoInMeasure P (fun i ω => F i ω j) l (fun _ => 0)) :
    TendstoInMeasure P F l (fun _ => 0) := by
  classical
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have hcoord (j : J) : Tendsto (fun i => P.real {ω | ε ≤ ‖F i ω j‖}) l (𝓝 0) := by
    have h := (tendstoInMeasure_iff_measureReal_norm.1 (hF j)) ε hε
    simpa only [Pi.zero_apply, sub_zero] using h
  have hsum : Tendsto (fun i => ∑ j : J, P.real {ω | ε ≤ ‖F i ω j‖}) l (𝓝 0) := by
    have h := tendsto_finsetSum Finset.univ (fun j _ => hcoord j)
    simpa only [Finset.sum_const_zero] using h
  apply squeeze_zero (g := fun i => ∑ j : J, P.real {ω | ε ≤ ‖F i ω j‖})
  · intro i
    exact measureReal_nonneg
  · intro i
    have hsub : {ω | ε ≤ ‖F i ω - 0‖} ⊆ ⋃ j : J, {ω | ε ≤ ‖F i ω j‖} := by
      intro ω hω
      simp only [sub_zero] at hω
      by_contra hn
      have hj (j : J) : ‖F i ω j‖ < ε := by
        have hn' : ω ∉ {ω | ε ≤ ‖F i ω j‖} := by
          intro hmem
          exact hn (Set.mem_iUnion.2 ⟨j, hmem⟩)
        exact lt_of_not_ge hn'
      have hlt : ‖F i ω‖ < ε := (pi_norm_lt_iff hε).2 hj
      exact (not_le_of_gt hlt) hω
    calc
      P.real {ω | ε ≤ ‖F i ω - 0‖} ≤ P.real (⋃ j : J, {ω | ε ≤ ‖F i ω j‖}) :=
        measureReal_mono hsub
      _ ≤ ∑ j : J, P.real {ω | ε ≤ ‖F i ω j‖} := measureReal_iUnion_fintype_le _
  · exact hsum

end EinsteinFull.External.DFGW
