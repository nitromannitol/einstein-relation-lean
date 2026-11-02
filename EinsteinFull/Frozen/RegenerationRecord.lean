import EinsteinFull.Frozen.RegenerationCoupling

namespace EinsteinFull

open EinsteinRelation

/-- The shifted path, future coins and BOTH reduced fields on x₁ ≥ -2R.
The blueprint's finite-time fallback is used only on the null infinite-time
event under the source coupling and its cited regeneration tail bound. -/
noncomputable def regenerationRecord {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (k : ℕ) (ωz : FieldPair d × Regeneration.CoupledSample d) :
    Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) :=
  Regeneration.Renewal.cycleRecord hd lam l k ωz

end EinsteinFull
