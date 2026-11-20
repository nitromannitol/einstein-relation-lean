import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import PDEFoundation.Ambient.Basic

/-!
# Smooth slab exit payoff

A one-dimensional smooth transition gives a bounded smooth function equal
to zero on the lower slab face and one on the upper slab face.
-/

open Set PDE

namespace EinsteinFull.Regeneration

/-- Smooth interpolation between the two force faces of a slab. -/
noncomputable def slabSmoothPayoff {d : ℕ} (i : Fin d) (x : PDE.Vec d) (R : ℝ)
    (z : PDE.Vec d) : ℝ :=
  Real.smoothTransition ((z i - x i + R) / (2 * R))

/-- The slab payoff is smooth. -/
theorem slabSmoothPayoff_smooth {d : ℕ} (i : Fin d) (x : PDE.Vec d) (R : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (slabSmoothPayoff i x R) := by
  apply Real.smoothTransition.contDiff.comp
  exact (((contDiff_apply ℝ ℝ i).sub contDiff_const).add contDiff_const).div_const _

/-- The slab payoff takes values in the unit interval. -/
theorem slabSmoothPayoff_mem_Icc {d : ℕ} (i : Fin d) (x : PDE.Vec d) (R : ℝ)
    (z : PDE.Vec d) : slabSmoothPayoff i x R z ∈ Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _, Real.smoothTransition.le_one _⟩

/-- The smooth slab payoff vanishes on the lower force face. -/
theorem slabSmoothPayoff_lower {d : ℕ} (i : Fin d) (x : PDE.Vec d) (R : ℝ)
    (z : PDE.Vec d) (hz : z i - x i = -R) : slabSmoothPayoff i x R z = 0 := by
  simp only [slabSmoothPayoff, hz, neg_add_cancel, zero_div, Real.smoothTransition.zero]

/-- The smooth slab payoff equals one on the upper force face. -/
theorem slabSmoothPayoff_upper {d : ℕ} (i : Fin d) (x : PDE.Vec d) (R : ℝ)
    (hR : 0 < R) (z : PDE.Vec d) (hz : z i - x i = R) : slabSmoothPayoff i x R z = 1 := by
  have h : (R + R) / (2 * R) = 1 := by field_simp; ring
  simp only [slabSmoothPayoff, hz, h, Real.smoothTransition.one]

end EinsteinFull.Regeneration
