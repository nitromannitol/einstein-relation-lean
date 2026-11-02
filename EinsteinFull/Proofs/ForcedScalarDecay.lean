import EinsteinFull.Closures.RootClosures

/-! Provider for `p:scalar`: the closed proof composed from the exact adopted graph
reductions in `EinsteinFull.Closures.RootClosures`. -/

namespace EinsteinFull.Proofs

open EinsteinFull.Blueprint

/-- `p:scalar`, composed from the exact adopted graph reductions. -/
theorem forced_scalar_decay : node_p_u3A_scalarStmt :=
  clr_cl_node_p_u3A_scalar

end EinsteinFull.Proofs
