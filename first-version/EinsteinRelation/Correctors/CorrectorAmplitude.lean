import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt

/-! # Corrector amplitude

The amplitude `𝒜_d(R)` of the local corrector moment bounds (`paper/main.tex` lines 686-689).
-/

namespace EinsteinRelation.Correctors

/-- The corrector amplitude `𝒜_d(R)` (`paper/main.tex` lines 686-689): `1` for `d ≥ 3`
and `√(log (2 + R))` for `d = 2`, for `R ≥ 1`. -/
noncomputable def correctorAmplitude (d : ℕ) (R : ℝ) : ℝ :=
  if 3 ≤ d then 1 else Real.sqrt (Real.log (2 + R))

end EinsteinRelation.Correctors
