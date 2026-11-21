import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Mathlib.MeasureTheory.Function.L2Space

/-! # Mean-square convergence implies convergence in measure

A family of square-integrable real random variables converging to zero in mean square also
converges to zero in measure.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.External.DFGW

variable {Ω ι : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {l : Filter ι}

/-- Mean-square convergence of real random variables implies convergence in measure. -/
theorem tendstoInMeasure_zero_of_integral_sq (F : ι → Ω → ℝ)
    (hF : ∀ i, MemLp (F i) 2 P)
    (hlim : Tendsto (fun i => ∫ ω, F i ω ^ 2 ∂P) l (𝓝 0)) :
    TendstoInMeasure P F l (fun _ => 0) := by
  apply tendstoInMeasure_iff_measureReal_norm.2
  intro ε hε
  have hε2 : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hupper : Tendsto (fun i => (∫ ω, F i ω ^ 2 ∂P) / ε ^ 2) l (𝓝 0) := by
    simpa only [zero_div] using hlim.div_const (ε ^ 2)
  apply squeeze_zero (g := fun i => (∫ ω, F i ω ^ 2 ∂P) / ε ^ 2)
  · intro i
    exact measureReal_nonneg
  · intro i
    have hsub : {ω | ε ≤ ‖F i ω - 0‖} ⊆ {ω | ε ^ 2 ≤ F i ω ^ 2} := by
      intro ω hω
      simp only [sub_zero, Real.norm_eq_abs] at hω
      change ε ^ 2 ≤ F i ω ^ 2
      have hsq := (sq_le_sq₀ hε.le (abs_nonneg (F i ω))).2 hω
      simpa only [sq_abs] using hsq
    have hmono : P.real {ω | ε ≤ ‖F i ω - 0‖} ≤ P.real {ω | ε ^ 2 ≤ F i ω ^ 2} :=
      measureReal_mono hsub
    have hmark := mul_meas_ge_le_integral_of_nonneg
      (μ := P) (f := fun ω => F i ω ^ 2) (ae_of_all P fun ω => sq_nonneg _)
      (hF i).integrable_sq (ε ^ 2)
    have hbound : P.real {ω | ε ^ 2 ≤ F i ω ^ 2} ≤
        (∫ ω, F i ω ^ 2 ∂P) / ε ^ 2 := (le_div_iff₀ hε2).2 (by simpa only [mul_comm] using hmark)
    exact hmono.trans hbound
  · exact hupper

end EinsteinFull.External.DFGW
