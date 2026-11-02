import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace EinsteinFull

/-- The critical correlation term `T_d` in Section 1. -/
noncomputable def criticalKernelTerm (d : ℕ) (lam : ℝ) (_hlam : lam ≠ 0) : ℝ :=
  if Even d then lam ^ d * Real.log (1 / |lam|) else |lam| ^ d

end EinsteinFull
