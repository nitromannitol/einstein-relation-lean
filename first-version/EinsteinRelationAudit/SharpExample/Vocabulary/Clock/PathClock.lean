import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Basic

/-! Restated from the library module `EinsteinRelation.Clock.PathClock`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

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
  · have h := intervalIntegral.integral_mono_on t.property hlo hf
      (fun u _ => (hb (γ u.toNNReal)).1)
    simpa only [pathClock, intervalIntegral.integral_const, sub_zero,
      smul_eq_mul, mul_comm] using h
  · have h := intervalIntegral.integral_mono_on t.property hf hhi
      (fun u _ => (hb (γ u.toNNReal)).2)
    simpa only [pathClock, intervalIntegral.integral_const, sub_zero,
      smul_eq_mul, mul_comm] using h
end EinsteinRelation.Clock
