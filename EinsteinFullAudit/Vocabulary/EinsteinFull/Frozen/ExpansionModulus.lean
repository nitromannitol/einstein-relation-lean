import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Vocabulary for `EinsteinFull.Frozen.ExpansionModulus`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinFull

/-- The explicit modulus in Section 1, on its stated positive domain. -/
noncomputable def expansionModulus (s : ℝ) (_hs : 0 < s)
    (_hsmall : s ≤ Real.exp (-1)) : ℝ :=
  Real.exp (-Real.sqrt (Real.log (1 / s)))

end EinsteinFull
