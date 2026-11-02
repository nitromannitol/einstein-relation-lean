import EinsteinFull.Closures.RootClosuresS3

/-! Provider for `p:tail`: the closed proof composed from the exact adopted graph
reductions in `EinsteinFull.Closures.RootClosuresS3`. -/

namespace EinsteinFull.Proofs

open EinsteinFull.Blueprint

/-- `p:tail`, composed from the exact adopted graph reductions. -/
theorem correlation_tail : node_p_u3A_tailStmt :=
  cls3_cl_node_p_u3A_tail

end EinsteinFull.Proofs
