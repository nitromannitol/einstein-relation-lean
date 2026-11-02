import EinsteinFull.Frozen.RegenerationNoReturn
import Mathlib.Probability.ConditionalProbability

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The annealed law conditioned on the source event D, on its positive-mass
domain. It retains the physical environment together with the path and coins. -/
noncomputable def regenerationConditionedLaw {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (_hK : Regeneration.HasProbabilityLaws Q.measure K)
    (_hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) :
    Measure (FieldPair d × Regeneration.CoupledSample d) :=
  ProbabilityTheory.cond (Regeneration.annealedCoupledLaw Q.measure K)
    (regenerationNoReturn hd (l / lam))

end EinsteinFull
