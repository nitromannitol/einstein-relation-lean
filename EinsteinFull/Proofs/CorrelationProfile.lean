import EinsteinFull.Closures.RootClosures

/-! Provider for `p:profile`: the closed proof composed from the exact adopted graph
reductions in `EinsteinFull.Closures.RootClosures`. -/

namespace EinsteinFull.Proofs

open EinsteinFull.Blueprint

/-- `p:profile`, composed from the exact adopted graph reductions. -/
theorem correlation_profile : node_p_u3A_profileStmt :=
  clr_cl_node_p_u3A_profile

end EinsteinFull.Proofs
