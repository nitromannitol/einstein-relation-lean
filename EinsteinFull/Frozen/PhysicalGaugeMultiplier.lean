import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

namespace EinsteinFull
open EinsteinRelation

/-- The literal physical-space gauge multiplier and its inverse at -lambda. -/
noncomputable def physicalGaugeMultiplier {d : ℕ} (i : Fin d) (lam : ℝ)
    (u : Vec d → ℂ) (x : Vec d) : ℂ :=
  (Real.exp (lam * x i) : ℂ) * u x

end EinsteinFull
