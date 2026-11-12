import EinsteinRelation.Regeneration.OccupationFromCoupledLocality
import EinsteinRelation.Regeneration.PastHalfSpaceVersionsFromLocality
import EinsteinRelation.Regeneration.KilledFutureVersionsFromLocality
import EinsteinRelation.Regeneration.CouplingCovarianceFromV2

/-! # Lemma 3.1 and Proposition 3.2 from the frozen literature inputs

Source `paper/main.tex:348–517`. Coupled locality and covariance, slice
factorization, conditional invariance, and iteration are proved internal
steps. The resulting theorems are conditional on the listed frozen
external inputs and have no hypothesis asserting a result of this paper.
-/

open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinRelation

/-- The internal coupled-locality obligation follows from the frozen
GMP diffusion locality input and the actual coupling construction. -/
theorem coupledKernelLocalityInput_of_gmp_locality (hLoc : External.GMPKernelLocality) :
    CoupledKernelLocalityInput := by
  intro d hd Λ₀ r₀ Q lam l δ hl0 hl1 hl _hδ0 _hδ1 P K hGMP
  have hR : 0 < l / lam := div_pos hl hl0
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam := regenDelta_pos hl0
  have hcov := Regeneration.Renewal.coupling_covariance_of_isGMPCouplingV2
    hLoc hd Q lam l δ hl0 hl1 hl P K hGMP
  rcases hGMP with ⟨hK, hm, hP, _hbits, hr, _hsupport, _hendpoint, hone⟩
  exact ⟨Regeneration.hasPastHalfSpaceVersions_of_gmp_locality hLoc hd Q lam hl0.le hl1
      P K hK hm hP _ hΔ δ _ hR _ hr hone,
    Regeneration.hasKilledPathBitFutureVersions_of_gmp_locality hLoc hd Q lam hl0.le hl1
      P K hK hm hP _ hΔ δ _ hR _ hr hone,
    hcov⟩

/-- Lemma 3.1, conditional on frozen GMP locality and regeneration tails.
All renewal arguments of the paper are proved. -/
theorem renewalLemma31Input_of_inputs (hLoc : External.GMPKernelLocality)
    (hTail : GMPCouplingTailsV2Input) : RenewalLemma31Input :=
  renewalLemma31Input_of_coupled_locality_and_tails
    (coupledKernelLocalityInput_of_gmp_locality hLoc) hTail

/-- Proposition 3.2, conditional on the listed frozen external inputs.
No internal paper result is an extra assumption. -/
theorem occupationStatement_of_inputs (hE : GMPCouplingExistsV2Input)
    (hTail : GMPCouplingTailsV2Input) (hGir : GirsanovEndpointStep)
    (hInv : UnforcedEnvironmentInvarianceStep) (hFam : External.GMPReducedFamilyExistence)
    (hLoc : External.GMPKernelLocality) :
    ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ), Entropy.OccupationStatement d hd Λ₀ r₀ :=
  occupationStatement_of_coupled_locality_and_frozen_inputs
    (coupledKernelLocalityInput_of_gmp_locality hLoc) hE hTail hGir hInv hFam hLoc


end EinsteinRelation
