import EinsteinRelation.MainTheorems

/-!
# Theorem 1.2 (paper label `t.main`): the solution

The statement below is the statement of `Challenge.lean`, word for word. It is elaborated here
in the environment of the library, where the definitions that it uses are the library's own;
the proof applies the library theorem `EinsteinRelation.mobility_rate`, whose hypotheses are the
same literature inputs in the same order.
-/

section MobilityRate

open MeasureTheory

namespace EinsteinRelation.Frozen

theorem _root_.EinsteinRelationAudit.MobilityRate.mobility_rate
    (h45 : EinsteinRelation.External.AKM.ScalarStationaryEstimate)
    (h46 : EinsteinRelation.External.AKM.ScalarPlanarL2Estimate)
    (h47 : EinsteinRelation.External.AKM.ScalarHeatDifferenceEstimate)
    (h68 : EinsteinRelation.External.AKM.FluxGradientEstimate)
    (h614 : EinsteinRelation.External.AKM.FluxStationaryEstimate)
    (h615 : EinsteinRelation.External.AKM.FluxPlanarL2Estimate)
    (h616 : EinsteinRelation.External.AKM.FluxHeatDifferenceEstimate)
    (h832 : EinsteinRelation.External.GilbargTrudinger.InteriorGradientEstimate)
    (h836 : EinsteinRelation.External.GilbargTrudinger.InteriorRegularRepresentative)
    (hdecay : EinsteinRelation.External.AKM.ParabolicSemigroupKernelDecay)
    (hreg : EinsteinRelation.External.AKM.ParabolicLargeScale)
    (hEll : EinsteinRelation.External.AKM.EllipticLargeScale)
    (hE1 : EinsteinRelation.External.AKM.ParabolicHeatKernel)
    (hH2 : EinsteinRelation.External.AKM.CorrectorWeakH2)
    (hAKM : EinsteinRelation.AKMFluxDecayLargeTime)
    (hFOT : EinsteinRelation.FukushimaDecompositionInput)
    (hGir : EinsteinRelation.GirsanovEndpointStep)
    (hInv : EinsteinRelation.UnforcedEnvironmentInvarianceStep)
    (hRF : EinsteinRelation.External.GMPReducedFamilyExistence)
    (hE : EinsteinRelation.GMPCouplingExistsV2Input)
    (hTail : EinsteinRelation.GMPCouplingTailsV2Input)
    (hLoc : EinsteinRelation.External.GMPKernelLocality)
    (hRV : EinsteinRelation.External.GMPReducedVelocityExistence)
    (hTC : EinsteinRelation.External.GMPTimeChangeLaw)
    (hPos : EinsteinRelation.External.GMPPhysicalVelocityPositive)
    (hErg : EinsteinRelation.External.GMPEnvironmentProcessErgodic)
    (hIP : EinsteinRelation.External.GMPReducedInvarianceAbar)
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ C lamStar : ℝ, 0 < lamStar ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d),
      IsGMPPhysicalFamily hd Q.ellipticity_parameter Q P →
      ∀ (covariance : Mat d), HasDiffusivity Q.measure (originLaw (P 0)) covariance →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lamStar →
      ∀ (velocity : Vec d), HasQuenchedVelocity Q.measure (originLaw (P lam)) velocity →
      euclideanNorm ((lam⁻¹ • velocity) - covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)))
        ≤ C * lam := by
  exact EinsteinRelation.mobility_rate h45 h46 h47 h68 h614 h615 h616 h832 h836 hdecay hreg hEll hE1
    hH2 hAKM hFOT hGir hInv hRF hE hTail hLoc hRV hTC hPos hErg hIP d hd Λ₀ r₀

end EinsteinRelation.Frozen

end MobilityRate
