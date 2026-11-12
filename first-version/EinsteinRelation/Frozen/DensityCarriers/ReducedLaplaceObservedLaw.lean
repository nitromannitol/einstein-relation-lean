import EinsteinRelation.Frozen.ValidAnnealedLawCarriers.AnnealedCoordinateJoint
import EinsteinRelation.Frozen.DensityCarriers.ReducedObservationAt
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Probability.Distributions.Exponential

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

namespace EinsteinRelation.Frozen.DensityCarriers

/-- The reduced environment law at an independent exponential time of positive rate. -/
def reducedLaplaceObservedLaw {d : ℕ} {hd : 2 ≤ d}
    (I : EinsteinRelation.Frozen.ValidAnnealedLawCarriers.CoordinatePathLawInput d hd)
    (s : {r : ℝ // 0 < r}) : Measure (FieldPair d) :=
  ((ProbabilityTheory.expMeasure s.1).prod
      (EinsteinRelation.Frozen.ValidAnnealedLawCarriers.annealedCoordinateJoint I)).map
    (fun z : ℝ × (FieldPair d × Path d) =>
      reducedObservationAt z.1.toNNReal z.2)

end EinsteinRelation.Frozen.DensityCarriers
