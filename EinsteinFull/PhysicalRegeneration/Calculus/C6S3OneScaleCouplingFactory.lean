import EinsteinFull.Calculus.C6S3OneScaleCouplingFactory
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS10BridgeIntegrability
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS1SplitGridFreshBits
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.C6S3OneScaleCouplingFactory`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open EinsteinRelation Regeneration MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
/-- The physical-kernel version of
`EinsteinFull.Blueprint.c6_s3_coupling_of_ae_endpoint_minorization`. -/
theorem c6_s3_coupling_of_ae_endpoint_minorization_phys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0.le h1 P)
    (L δ : ℝ) (hL : 0 < L) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hminor : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, ENNReal.ofReal δ • ProbabilityTheory.cond (volume : Measure (Vec d))
          (endpointBall (Renewal.forceCoord hd) (L / lam) x) ≤
        (Renewal.killedSegmentLaw (Renewal.regenDelta lam) (L / lam)
          (Renewal.forceCoord hd) P x ω).map (fun γ : Path d => γ (Renewal.regenDelta lam))) :
    ∃ K : CoupledQuenchedLaws d, IsRegenerationCouplingPhys hd Q lam L δ h0.le h1 P K := by
  have hgood := hP.and hminor
  obtain ⟨N, hsub, hNm, hNzero⟩ := exists_measurable_superset_of_null (ae_iff.mp hgood)
  have hGae : ∀ᵐ ω ∂Q.measure, ω ∈ Nᶜ := by
    apply ae_iff.mpr
    simpa using hNzero
  have hGgood := fun ω (hω : ω ∈ Nᶜ) => not_not.mp (fun hbad => hω (hsub hbad))
  have hprob : ∀ ω ∈ Nᶜ, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)) := by
    intro ω hω x
    obtain ⟨_, r, hr⟩ := (hGgood ω hω).1
    rw [hr x]
    exact r.pathLaw_isMarkovKernel.isProbabilityMeasure x
  have hstart : ∀ ω ∈ Nᶜ, ∀ x : Vec d, ∀ᵐ γ ∂P (x, ω), γ 0 = x := by
    intro ω hω x
    obtain ⟨_, r, hr⟩ := (hGgood ω hω).1
    rw [hr x]
    exact r.pathLaw_starts_at x
  obtain ⟨K, _, hK⟩ := SbxS1SplitGridFreshBits.exists_markov_splitGrid_isGMPCouplingV2_phys
    hd Q.ellipticity_parameter Q lam L δ h0 h1 hL P hP Nᶜ hNm.compl hGae
    hprob (fun ω hω => (hGgood ω hω).2) hδ0 hδ1 hstart
  exact ⟨K, hK⟩

end EinsteinFull.Blueprint
