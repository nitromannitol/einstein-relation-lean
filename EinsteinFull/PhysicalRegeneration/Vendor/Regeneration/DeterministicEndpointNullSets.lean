import EinsteinRelation.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI

/-!
# Physical-kernel version of
`EinsteinRelation.Regeneration.DeterministicEndpointNullSets`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinRelation.Regeneration
/-- The physical-kernel version of `EinsteinRelation.Regeneration.ae_at_endpoint_of_product_ae`. -/
theorem ae_at_endpoint_of_product_ae_phys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P)
    (t : ℝ≥0) (ht : 0 < t) (p : Vec d × FieldPair d → Prop)
    (hp : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure, p xω) :
    ∀ᵐ ωz ∂annealedCoupledLaw Q.measure K, p (ωz.2.1 t, ωz.1) := by
  have hac := map_endpoint_environment_absolutelyContinuous Q.measure P K hK hpath t
    ((map_pathPosition_absolutelyContinuous_of_isGMPReducedKernel_phys hd Q.ellipticity_parameter
      Q lam h0 h1 P hP t ht).mono fun _ h => h 0)
  exact ae_of_ae_map
    ((((continuous_eval_const t).measurable.comp measurable_snd.fst).prodMk
      measurable_fst).aemeasurable) (hac.ae_le hp)

end EinsteinRelation.Regeneration
