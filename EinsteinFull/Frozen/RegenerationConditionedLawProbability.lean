import EinsteinFull.Frozen.RegenerationConditionedLaw

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- Conditioning the actual annealed probability law on positive-mass D
is again a probability law. -/
theorem regenerationConditionedLaw_probability {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) :
    IsProbabilityMeasure (regenerationConditionedLaw hd Q lam l K hK hD) := by
  letI := Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK
  exact ProbabilityTheory.cond_isProbabilityMeasure hD

end EinsteinFull
