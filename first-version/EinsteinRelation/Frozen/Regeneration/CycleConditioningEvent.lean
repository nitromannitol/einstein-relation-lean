import EinsteinRelation.Regeneration.Construction

namespace EinsteinRelation.Regeneration

/-- The source no-backtracking event on the actual annealed environment/sample space. -/
def cycleConditioningEvent {d : ℕ} (hd : 2 ≤ d) (R : ℝ) :
    Set (FieldPair d × CoupledSample d) :=
  {ωz | NoBacktracking R ωz.2.1 ⟨0, by omega⟩}

end EinsteinRelation.Regeneration
