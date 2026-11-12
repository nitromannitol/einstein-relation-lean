import EinsteinRelation.Environment.Basic

namespace EinsteinRelation.Correctors

/-- The coefficient-only observation sigma algebra on a reduced environment. -/
def reducedCoefficientObservationSigma {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace (FieldPair d) :=
  ⨆ x : U, MeasurableSpace.comap (fun ω : FieldPair d => ω.1 x) inferInstance

end EinsteinRelation.Correctors
