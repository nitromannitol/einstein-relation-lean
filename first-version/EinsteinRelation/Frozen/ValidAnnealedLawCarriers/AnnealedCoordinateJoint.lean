import EinsteinRelation.Frozen.ValidAnnealedLawCarriers.CoordinatePathLawInput
import EinsteinRelation.Probability.ValidAnnealedLawSupport

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Frozen.ValidAnnealedLawCarriers

open EinsteinRelation.Probability.ValidAnnealedLawSupport

/-- The annealed joint environment and physical path law at the origin. -/
def annealedCoordinateJoint {d : ℕ} {hd : 2 ≤ d} (I : CoordinatePathLawInput d hd) :
    Measure (FieldPair d × Path d) :=
  annealedJointOnProbabilityFibers I.Q (originLaw I.P) I.origin_probability

end EinsteinRelation.Frozen.ValidAnnealedLawCarriers
