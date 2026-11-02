import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.RegenerationConditionedLaw

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull

open EinsteinRelation

/-- The actual conditional probability p_n of τ₁ = nΔ. -/
noncomputable def regenerationLatticeMass {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) (n : ℕ) : ℝ :=
  (regenerationConditionedLaw hd Q lam l K hK hD).real {ωz |
    regenerationTime hd lam l 1 ωz.2 =
      (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}

end EinsteinFull
