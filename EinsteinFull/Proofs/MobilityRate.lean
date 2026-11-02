import EinsteinFull.Closures.RootClosuresS3

/-! Provider for `t.main`: the closed proof composed from the exact adopted graph
reductions in `EinsteinFull.Closures.RootClosuresS3`. -/

namespace EinsteinFull.Proofs

open EinsteinFull.Blueprint

/-- `t.main`, composed from the exact adopted graph reductions. -/
theorem mobility_rate : node_t_u2E_mainStmt :=
  cls3_cl_node_t_u2E_main

end EinsteinFull.Proofs
