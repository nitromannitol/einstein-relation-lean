import EinsteinFull.Closures.RootClosuresS3

/-! CoarseGraining declares a second instance `Homogenization.instMeasurableSpaceMat` (the product
σ-algebra on `Mat d`). The frozen statement was elaborated with the Borel instance
`EinsteinRelation.instMeasurableSpaceMat`; this priority makes the sealed anchor, which imports this
file, elaborate the frozen statement exactly as frozen (checked by `exact` and by the root mirror audit). -/

attribute [instance 2000] EinsteinRelation.instMeasurableSpaceMat

/-! Provider for `rt:renewal`: the closed proof composed from the exact adopted graph
reductions in `EinsteinFull.Closures.RootClosuresS3`. -/

namespace EinsteinFull.Proofs

open EinsteinFull.Blueprint

/-- `rt:renewal`, composed from the exact adopted graph reductions. -/
theorem uniform_lattice_renewal : node_rt_u3A_renewalStmtV2 :=
  cls3_cl_node_rt_u3A_renewal

end EinsteinFull.Proofs
