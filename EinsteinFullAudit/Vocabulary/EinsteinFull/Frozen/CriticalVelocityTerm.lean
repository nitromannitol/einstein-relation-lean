import Mathlib.Analysis.SpecialFunctions.Log.Basic
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.CriticalKernelTerm

/-! Vocabulary for `EinsteinFull.Frozen.CriticalVelocityTerm`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinFull

/-- The critical velocity term `S_d` in Section 1. -/
noncomputable def criticalVelocityTerm (d : ℕ) (lam : ℝ) (hlam : lam ≠ 0) : ℝ :=
  lam * criticalKernelTerm d lam hlam

end EinsteinFull
