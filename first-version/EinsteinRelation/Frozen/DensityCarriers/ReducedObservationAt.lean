import EinsteinRelation.Environment.Reduction
import EinsteinRelation.Diffusion.Basic

open EinsteinRelation
open scoped NNReal

noncomputable section

namespace EinsteinRelation.Frozen.DensityCarriers

/-- The reduced environment observed at time `t` along a continuous path. -/
def reducedObservationAt {d : ℕ} (t : ℝ≥0)
    (z : FieldPair d × Path d) : FieldPair d :=
  reduce (translate (pathPosition t z.2) z.1)

end EinsteinRelation.Frozen.DensityCarriers
