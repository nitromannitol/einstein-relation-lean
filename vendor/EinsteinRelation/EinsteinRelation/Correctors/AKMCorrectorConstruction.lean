import EinsteinRelation.Correctors.AKMSublinearGradientConstruction
import EinsteinRelation.Correctors.AKMStationarityFromIdentification
import EinsteinRelation.Correctors.AKMHarmonicTransport
import EinsteinRelation.Correctors.AKMCorrectorPackaging

/-!
# The actual canonical AKM corrector

Source: `paper/main.tex:693-702,727-729`. The scalar potential is constructed
under the raw coefficient law, with its weak gradient and sublinearity.
Canonical identification supplies stationarity, harmonicity and integrable
cell flux. No realization or corrector characterization is assumed.
-/
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport

/-- The existing Poincaré literature input suffices to construct all AKM
corrector characterization fields for the actual canonical gradient. -/
theorem exists_canonicalAKMSpatialRealization
    (hP : BallPoincareEstimate) {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    Nonempty (CanonicalAKMSpatialRealization Q i) := by
  obtain ⟨g, hg, hid, hpot⟩ := exists_akm_sublinear_characterized_gradient hP Q i
  exact exists_akmSpatialRealization_of_characterized_gradient Q i g hg hid hpot
    (fun z => ae_akm_stationary_of_canonical_gradient Q i g hg hid (latticeShift z))
    (ae_akm_harmonic_of_canonical_gradient Q i g hg hid)

end EinsteinRelation.Correctors
