import EinsteinFull.Frozen.CriticalKernelTerm

namespace EinsteinFull

/-- The critical velocity term `S_d` in Section 1. -/
noncomputable def criticalVelocityTerm (d : ℕ) (lam : ℝ) (hlam : lam ≠ 0) : ℝ :=
  lam * criticalKernelTerm d lam hlam

end EinsteinFull
