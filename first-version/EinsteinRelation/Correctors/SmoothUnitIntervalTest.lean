import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-! Auxiliary time-continuity and test-function estimates; source `paper/main.tex:808–848`. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

theorem exists_smooth_unit_integral_test_Ioo {a b : ℝ} (hab : a < b) :
    ∃ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Set.Ioo a b ∧ (∫ t : ℝ, η t) = 1 := by
  let f : ContDiffBump ((a + b) / 2) :=
    { rIn := (b - a) / 8, rOut := (b - a) / 4, rIn_pos := by linarith,
      rIn_lt_rOut := by linarith }
  have hr : f.rOut = (b - a) / 4 := rfl
  have hsupp : tsupport (f.normed volume) ⊆ Set.Ioo a b := by
    rw [f.tsupport_normed_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at hx
    exact ⟨by linarith [hx.1, hr], by linarith [hx.2, hr]⟩
  exact ⟨f.normed volume, f.contDiff_normed (μ := volume),
    f.hasCompactSupport_normed (μ := volume), hsupp, f.integral_normed (μ := volume)⟩

end EinsteinRelation.Correctors
