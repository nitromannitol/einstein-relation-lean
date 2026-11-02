import EinsteinRelation.Environment.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Instances.NNReal.Lemmas

/-! # The clock along an actual continuous path

`paper/main.tex`, `eq.clock-definition` and its deterministic bounds, lines
214–218. Nonnegative-time paths are extended to real integration variables by
`Real.toNNReal`, exactly as in the canonical martingale-problem definition.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinRelation.Clock

/-- The additive clock obtained by integrating a spatial density along a path. -/
noncomputable def pathClock {d : ℕ} (μ : Vec d → ℝ)
    (γ : C(ℝ≥0, Vec d)) (t : ℝ≥0) : ℝ :=
  ∫ u in (0 : ℝ)..(t : ℝ), μ (γ u.toNNReal)

/-- A bounded density gives the same deterministic bounds on the clock rate. -/
theorem pathClock_bounds {d : ℕ} (μ : Vec d → ℝ) (hμ : Continuous μ)
    (lo hi : ℝ) (hb : ∀ x, lo ≤ μ x ∧ μ x ≤ hi)
    (γ : C(ℝ≥0, Vec d)) (t : ℝ≥0) :
    lo * (t : ℝ) ≤ pathClock μ γ t ∧ pathClock μ γ t ≤ hi * (t : ℝ) := by
  have hf : IntervalIntegrable (fun u : ℝ => μ (γ u.toNNReal)) volume 0 (t : ℝ) :=
    (hμ.comp (γ.continuous.comp continuous_real_toNNReal)).intervalIntegrable _ _
  have hlo : IntervalIntegrable (fun _ : ℝ => lo) volume 0 (t : ℝ) :=
    intervalIntegrable_const
  have hhi : IntervalIntegrable (fun _ : ℝ => hi) volume 0 (t : ℝ) :=
    intervalIntegrable_const
  constructor
  · have h : ∫ _ in (0 : ℝ)..(t : ℝ), lo ≤ ∫ u in (0 : ℝ)..(t : ℝ), μ (γ u.toNNReal) :=
      intervalIntegral.integral_mono_on t.property hlo hf
        (fun u _ => (hb (γ u.toNNReal)).1)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm (t : ℝ) lo] at h
    exact h
  · have h : ∫ u in (0 : ℝ)..(t : ℝ), μ (γ u.toNNReal) ≤ ∫ _ in (0 : ℝ)..(t : ℝ), hi :=
      intervalIntegral.integral_mono_on t.property hf hhi
        (fun u _ => (hb (γ u.toNNReal)).2)
    rw [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_comm (t : ℝ) hi] at h
    exact h

end EinsteinRelation.Clock
