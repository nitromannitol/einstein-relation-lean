import EinsteinFull.Frozen.RegenerationCoupling

namespace EinsteinFull

open EinsteinRelation

/-- The actual no-return event D, relative to the initial point. -/
def regenerationNoReturn {d : ℕ} (hd : 2 ≤ d) (R : ℝ) :
    Set (FieldPair d × Regeneration.CoupledSample d) :=
  {ωz | Regeneration.NoBacktracking R ωz.2.1 (Regeneration.Renewal.forceCoord hd)}

end EinsteinFull
