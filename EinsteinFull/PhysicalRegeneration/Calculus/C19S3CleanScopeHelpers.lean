import EinsteinFull.Calculus.C19S3CleanScopeHelpers
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.C19S3CleanScopeHelpers`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration
/-- The physical-kernel version of
`EinsteinFull.Blueprint.c19_s3_clean_future_one_of_future_kernel`. -/
theorem c19_s3_clean_future_one_of_future_kernel_phys
    (hFutureKernel : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (hcov : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
      (K p).map (recenterSample p.1) = K (0, translate p.1 p.2)) :
    ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ B : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | y (Renewal.forceCoord hd) - 2 * (l / lam) ≤
        x (Renewal.forceCoord hd)}] B ∧
      (fun ω => ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd)
        (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω)) =ᵐ[Q.measure] B := by
  obtain ⟨B, hB, hBo⟩ := hFutureKernel d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1
    P K hK (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩
  filter_upwards [Measure.ae_ae_of_ae_prod hcov] with y hy
  have hmap : ∀ᵐ ω ∂Measure.map (translate y) Q.measure,
      (∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) (fun _ => (1 : ℝ))
        ((0, ω), z) ∂K (0, ω)) = B ω := by
    rw [Q.stationary y]
    exact hBo
  have ht := ae_of_ae_map (Probability.measurable_translate y).aemeasurable hmap
  refine ⟨fun ω => B (translate y ω), ?_, ?_⟩
  · apply (hB.comp (Probability.measurable_translate_local y _)).mono
      (Probability.localSigma_mono ?_) le_rfl
    rintro x ⟨z, hz, rfl⟩
    change -2 * (l / lam) ≤ z (Renewal.forceCoord hd) at hz
    change y (Renewal.forceCoord hd) - 2 * (l / lam) ≤ (y + z) (Renewal.forceCoord hd)
    simp only [Pi.add_apply]
    linarith
  · filter_upwards [hy, ht] with ω hc hb
    have hmrec : Measurable (recenterSample y) :=
      measurable_recenterSample.comp (measurable_const.prodMk measurable_id)
    have hmtest : Measurable (fun z => killedFutureTest (l / lam) (Renewal.forceCoord hd)
        (fun _ => (1 : ℝ)) ((0, translate y ω), z)) :=
      (measurable_killedFutureTest (l / lam) (Renewal.forceCoord hd) (fun _ => (1 : ℝ))
        measurable_const).comp (measurable_const.prodMk measurable_id)
    rw [← hb, ← hc, integral_map hmrec.aemeasurable hmtest.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
      (c19_clean_killedFutureTest_recenter_origin (l / lam) (Renewal.forceCoord hd)
        (fun _ => (1 : ℝ)) y ω z).symm)

end EinsteinFull.Blueprint
