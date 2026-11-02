import EinsteinFull.Closures.RootClosures

/-! Provider for `p:late`: the closed proof composed from the exact adopted graph
reductions in `EinsteinFull.Closures.RootClosures`. -/

namespace EinsteinFull.Proofs

open EinsteinFull.Blueprint

/-- `p:late`, composed from the exact adopted graph reductions. -/
theorem late_force_replacement : node_p_u3A_lateStmt :=
  clr_cl_node_p_u3A_late

end EinsteinFull.Proofs
