import EinsteinRelation.Clock.PathClock
import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Environment.Bounds

/-! # The nonnegative physical clock and its divergence

`paper/main.tex:214–228`. The actual clock integrates `exp(-2V)` along a continuous
path. Its lower bound, rather than a new asymptotic premise, makes it divergent.
-/

open Filter MeasureTheory
open scoped NNReal Topology

namespace EinsteinRelation.Clock

/-- Positive lower and upper density bounds force the actual clock to diverge. -/
theorem pathClock_tendsto_atTop {d : ℕ} (μ : Vec d → ℝ) (hμ : Continuous μ)
    (lo hi : ℝ) (hlo : 0 < lo) (hb : ∀ x, lo ≤ μ x ∧ μ x ≤ hi)
    (γ : Path d) : Tendsto (pathClock μ γ) atTop atTop := by
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hlin : Tendsto (fun t : ℝ≥0 => lo * (t : ℝ)) atTop atTop :=
    hcoe.const_mul_atTop hlo
  exact tendsto_atTop_mono (fun t => (pathClock_bounds μ hμ lo hi hb γ t).1) hlin

/-- The physical clock as a map on nonnegative time. -/
noncomputable def physicalPathClock {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (t : ℝ≥0) : ℝ≥0 :=
  ⟨pathClock (clockDensity ω) γ t,
    intervalIntegral.integral_nonneg t.property
      (fun u _ => (clockDensity_pos ω (γ u.toNNReal)).le)⟩

@[simp] theorem coe_physicalPathClock {d : ℕ} (ω : FieldPair d) (γ : Path d) (t : ℝ≥0) :
    (physicalPathClock ω γ t : ℝ) = pathClock (clockDensity ω) γ t := rfl

/-- Bounded physical potential gives divergence of the actual nonnegative clock. -/
theorem physicalPathClock_tendsto_atTop {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hV : ∀ x, |ω.2 x| ≤ L) :
    Tendsto (physicalPathClock ω γ) atTop atTop := by
  apply NNReal.tendsto_coe_atTop.mp
  exact pathClock_tendsto_atTop (clockDensity ω) (reduce ω).2.continuous
    (Real.exp (-2 * L)) (Real.exp (2 * L)) (Real.exp_pos _)
    (fun x => clockDensity_bounds ω x L (hV x)) γ

end EinsteinRelation.Clock
