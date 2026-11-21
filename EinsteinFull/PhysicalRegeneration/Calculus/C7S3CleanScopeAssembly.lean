import EinsteinFull.Calculus.C7S3CleanScopeAssembly
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Calculus.C19S3CleanScopeHelpers
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.C7S3CleanScopeAssembly`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open EinsteinRelation Regeneration MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open scoped Classical in
/-- The physical-kernel version of `EinsteinFull.Blueprint.c7_clean_burn_endpoint_of_local_past`. -/
theorem c7_clean_burn_endpoint_of_local_past_phys
    (hFutureKernel : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (hcov : ∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
      (K p).map (recenterSample p.1) = K (0, translate p.1 p.2))
    (m k : ℕ) (E : Set (CoupledSample d)) (hE : MeasurableSet E) (η : ℝ)
    (hmean : ∀ᵐ y ∂(volume : Measure (Vec d)), η ≤ ∫ ω,
      ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) (fun _ => (1 : ℝ))
        ((y, ω), z) ∂K (y, ω) ∂Q.measure)
    (hApast : ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | x (Renewal.forceCoord hd) ≤
        y (Renewal.forceCoord hd) - 4 * (l / lam)}] A ∧
      (fun ω => ∫ z, E.indicator (fun _ => (1 : ℝ)) z *
        (if y ∈ endpointBall (Renewal.forceCoord hd) (l / lam)
          (z.1 (((m + k : ℕ) : ℝ≥0) * Renewal.regenDelta lam)) then 1 else 0)
        ∂K (0, ω)) =ᵐ[Q.measure] A) :
    η * (∫ ω, ∫ z, E.indicator (fun _ => (1 : ℝ)) z ∂K (0, ω) ∂Q.measure) ≤
      ∫ ω, ∫ z, E.indicator (fun _ => (1 : ℝ)) z *
        endpointAverage (Renewal.forceCoord hd) (l / lam)
          (z.1 (((m + k : ℕ) : ℝ≥0) * Renewal.regenDelta lam))
          (fun y => ∫ w, killedFutureTest (l / lam) (Renewal.forceCoord hd)
            (fun _ => (1 : ℝ)) ((y, ω), w) ∂K (y, ω)) ∂K (0, ω) ∂Q.measure := by
  have hlR : l ≤ l / lam := (le_div_iff₀ h0).2 (by nlinarith [mul_nonneg hl.le (sub_nonneg.mpr h1)])
  have hgap : r₀ < 2 * (l / lam) := by linarith
  exact c15_clean_burn_endpoint_average_lower_of_local_versions Q K hK.1
    (Renewal.regenDelta lam) (l / lam) (div_pos hl h0) (Renewal.forceCoord hd)
    m k E hE hgap η hmean hApast
    (c19_s3_clean_future_one_of_future_kernel_phys hFutureKernel hd Q lam h0 h1 l δ hl
      hsep hδ0 hδ1 P K hK hcov)

end EinsteinFull.Blueprint
