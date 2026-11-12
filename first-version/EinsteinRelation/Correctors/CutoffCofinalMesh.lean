import EinsteinRelation.Correctors.CutoffNearestMesh
import Mathlib.Analysis.SpecificLimits.Basic

/-! Source: `paper/main.tex:722,756`. The nearest original cutoff indices
remain cofinal under any fixed positive physical time dilation. -/
open Filter
namespace EinsteinRelation.Correctors

/-- Both the integer and reciprocal original cutoff indices remain
cofinal after a positive rescaling of physical time. -/
theorem tendsto_rescaled_cutoff_mesh_atTop (c : ℝ) (hc : 0 < c) :
    Tendsto (fun n : ℕ => ⌊c * ((n : ℝ) + 1)⌋₊) atTop atTop ∧
      Tendsto (fun n : ℕ => ⌊((n : ℝ) + 1) / c⌋₊) atTop atTop := by
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 tendsto_natCast_atTop_atTop
  constructor
  · exact tendsto_nat_floor_atTop.comp (hn.const_mul_atTop hc)
  · exact tendsto_nat_floor_atTop.comp (hn.atTop_div_const hc)

end EinsteinRelation.Correctors
