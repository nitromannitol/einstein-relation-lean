import EinsteinFull.Closures.RootClosuresS3

/-! Provider for `sharp.example`: the closed proof composed from the exact adopted graph
reductions in `EinsteinFull.Closures.RootClosuresS3`. -/

namespace EinsteinFull.Proofs

open EinsteinFull.Blueprint

/-- `sharp.example`, composed from the exact adopted graph reductions. -/
theorem sharp_example : node_sharp_u2E_exampleStmt :=
  cls3_cl_node_sharp_u2E_example

end EinsteinFull.Proofs
