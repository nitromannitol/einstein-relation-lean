import EinsteinRelation.Correctors.CorrectorMomentsFromLiterature

/-! # The production gradient step from the complete Lemma 5.1

Source: `paper/main.tex:709-716,718-745`. Project the gradient assertion of
Lemma 5.1 using the constructed source mollifier. All laws, representatives,
norms and constants are those of the existing production step.
-/

namespace EinsteinRelation

open Correctors External.AKM External.GilbargTrudinger
open Correctors.NormalizedSpatialRepresentativeSupport

/-- The gradient assertion of Lemma 5.1, conditional only on its eleven
frozen literature inputs, in the form consumed by the mobility closure. -/
theorem correctorGradientMoments_of_frozen_inputs
    (h45 : ScalarStationaryEstimate) (h46 : ScalarPlanarL2Estimate)
    (h47 : ScalarHeatDifferenceEstimate) (h68 : FluxGradientEstimate)
    (h614 : FluxStationaryEstimate) (h615 : FluxPlanarL2Estimate)
    (h616 : FluxHeatDifferenceEstimate) (hP : BallPoincareEstimate)
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative) : CorrectorGradientMoments := by
  intro d hd Λ₀ r₀ m hm
  letI : Fact (2 ≤ d) := ⟨hd⟩
  obtain ⟨C, hC⟩ := correctorMoments_of_literature
    h45 h46 h47 h68 h614 h615 h616 hP h817 h832 h836 d Λ₀ r₀ m hm
  exact ⟨C, fun Q => (hC Q (canonicalSourceMollifier d)).1⟩

end EinsteinRelation
