import EinsteinFull.External.DFGW.RealBrownianCharacteristic
import EinsteinFull.External.Draft.DFGWInvarianceV2
import Mathlib.MeasureTheory.Integral.Pi

/-! # Independent Brownian coordinates

A finite family of real Brownian paths defines a continuous vector-valued path under the product
of their laws.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation MarkovProcess
open scoped NNReal BigOperators

namespace EinsteinFull.External.DFGW

/-- Assemble a family of real paths into a vector-valued path. -/
def coordinatePaths {d : ℕ} (γ : Fin d → ContinuousPath ℝ) : Path d :=
  ContinuousMap.pi γ

/-- Assembling finitely many paths is continuous in the compact-open topologies. -/
theorem continuous_coordinatePaths (d : ℕ) : Continuous (coordinatePaths (d := d)) := by
  apply ContinuousMap.continuous_of_continuous_uncurry
  apply continuous_pi
  intro i
  exact continuous_eval.comp ((continuous_apply i).comp continuous_fst |>.prodMk
    continuous_snd)

/-- The law obtained by assembling independent standard real Brownian paths. -/
noncomputable def independentBrownianPaths (d : ℕ) : Measure (Path d) :=
  (Measure.pi (fun _ : Fin d => brownianMotion 0)).map coordinatePaths

instance (d : ℕ) : IsProbabilityMeasure (independentBrownianPaths d) := by
  unfold independentBrownianPaths
  infer_instance

end EinsteinFull.External.DFGW
