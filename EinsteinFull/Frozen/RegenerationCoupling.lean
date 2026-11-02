import EinsteinFull.Frozen.EnvironmentLaw
import EinsteinRelation.Regeneration.RenewalCarriers

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The actual GMP/Shen split coupling, reusing the blueprint's full
one-interval killed-bridge characterization. No renewal or locality
conclusion is included in this predicate. -/
abbrev IsRegenerationCoupling {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) : Prop :=
  Regeneration.Renewal.IsGMPCouplingV2 hd Q.ellipticity_parameter Q
    lam l δ h₀ h₁ P K

end EinsteinFull
