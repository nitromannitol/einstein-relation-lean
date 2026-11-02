import EinsteinFull.Frozen.RegenerationCoupling

open scoped NNReal ENNReal

namespace EinsteinFull

open EinsteinRelation

/-- The literal path-and-coin trial time, including the possible value infinity. -/
noncomputable def regenerationTime {d : ℕ} (hd : 2 ≤ d) (lam l : ℝ)
    (k : ℕ) (z : Regeneration.CoupledSample d) : ℝ≥0∞ :=
  Regeneration.regenerationTime (Regeneration.Renewal.regenDelta lam)
    lam (l / lam) z (Regeneration.Renewal.forceCoord hd) k

end EinsteinFull
