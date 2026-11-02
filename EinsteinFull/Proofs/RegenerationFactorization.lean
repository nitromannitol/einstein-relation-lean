import EinsteinFull.Closures.RootClosuresS3

/-! CoarseGraining declares a second instance `Homogenization.instMeasurableSpaceMat` (the product
σ-algebra on `Mat d`). The frozen statement was elaborated with the Borel instance
`EinsteinRelation.instMeasurableSpaceMat`; this priority makes the sealed anchor, which imports this
file, elaborate the frozen statement exactly as frozen (checked by `exact` and by the root mirror audit). -/

attribute [instance 2000] EinsteinRelation.instMeasurableSpaceMat

/-! Provider for `app:factorization`: the closed proof composed from the exact adopted graph
reductions in `EinsteinFull.Closures.RootClosuresS3`. -/

namespace EinsteinFull.Proofs

open EinsteinFull.Blueprint

/-- `app:factorization`, composed from the exact adopted graph reductions. -/
theorem regeneration_factorization : node_app_u3A_factorizationStmtV2 :=
  cls3_cl_node_app_u3A_factorization

end EinsteinFull.Proofs
