import EinsteinRelation.Regeneration.KilledFutureConditionalMean
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinRelation.Regeneration.KilledFutureConditionalMean`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinRelation.Regeneration
/-- The physical-kernel version of
`EinsteinRelation.Regeneration.ae_origin_start_of_isGMPReducedKernel`. -/
theorem ae_origin_start_of_isGMPReducedKernel_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ p ∂annealedCoupledLaw Q.measure K, p.2.1 0 = 0 := by
  apply Measure.ae_compProd_of_ae_ae
    (measurableSet_eq_fun ((continuous_eval_const 0).measurable.comp measurable_snd.fst)
      measurable_const)
  filter_upwards [hK.1, hpath.1, hP] with ω hp hm hω
  have : IsProbabilityMeasure (originCoupledLaw K ω) := hp
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  obtain ⟨_, r, hr⟩ := hω
  have hstarts : ∀ᵐ γ ∂P (0, ω), γ 0 = 0 := by
    rw [hr 0]
    exact r.pathLaw_starts_at 0
  rw [← hm] at hstarts
  exact ae_of_ae_map measurable_fst.aemeasurable hstarts

end EinsteinRelation.Regeneration
