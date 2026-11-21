import EinsteinFull.Calculus.C7S3IndependenceAssembly
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5CouplingAnalyticRecenter
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5EndpointAverageTransport
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5Independence
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS9CouplingAlgebraRecenter
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_endpoint_u2D_disintegration
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.C6S3SuppliedPathRecenter
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.CoupledEnvironmentRegularity
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.C7S3IndependenceAssembly`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Regeneration.Renewal
open EinsteinRelation.External.GantertSection7Support
/-- The physical-kernel version of
`EinsteinFull.Blueprint.c7_s3_independence_assuming_supplied_path_recenter`. -/
theorem c7_s3_independence_assuming_supplied_path_recenter_phys
    (h1 : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt_phys)
    (h2 : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (h3 : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (h4 : node_app_u3A_regen_u2D_tailsStmt_phys)
    (h5 : node_app_u3A_factorization_u23_slicesStmt_phys)
    (h6 : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys)
    (hcov : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K →
      ∀ᵐ a ∂(volume : Measure (Vec d)),
        (∀ᵐ η ∂Q.measure, P (0, η) = sbxS9RecenteredPathLaws P a (0, η)) ∧
        ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
          P p = sbxS9RecenteredPathLaws P a p) :
    node_app_u3A_factorization_u23_independenceStmtV2_phys :=
  EndpointAverageTransport.independence_assuming_original_path_covariance_phys
    h1 h2 h3 h4 h5 h6 hcov

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c7_s3_independence_of_all_start_recenter`. -/
theorem c7_s3_independence_of_all_start_recenter_phys
    (c6_s3_all_start_recenter_covariance : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
      (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
      ∀ (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
      IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K →
      ∀ᵐ a ∂(volume : Measure (Vec d)), ∀ᵐ η ∂Q.measure,
        ∀ x : Vec d, P (x, η) = sbxS9RecenteredPathLaws P a (x, η))
    (h1 : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt_phys)
    (h2 : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (h3 : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (h4 : node_app_u3A_regen_u2D_tailsStmt_phys)
    (h5 : node_app_u3A_factorization_u23_slicesStmt_phys)
    (h6 : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys) :
    node_app_u3A_factorization_u23_independenceStmtV2_phys := by
  apply c7_s3_independence_assuming_supplied_path_recenter_phys h1 h2 h3 h4 h5 h6
  intro d hd Λ₀ r₀ Q lam h0 hlam l δ hl hr hδ hδ1 P K hK
  filter_upwards [c6_s3_all_start_recenter_covariance d hd Λ₀ r₀ Q lam h0 hlam l δ
    hl hr hδ hδ1 P K hK] with a hall
  constructor
  · filter_upwards [hall] with η hη
    exact hη 0
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hall] with p hp
    exact hp p.1

/-- The physical-kernel version of
`EinsteinFull.Blueprint.c7_s3_independence_of_requested_identification`. -/
theorem c7_s3_independence_of_requested_identification_phys
    (requested_s3_supplied_gantert_c0_fdd : ∀ {d : ℕ} (hd : 2 ≤ d) (Λ : ℝ)
      (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω) (lam : ℝ)
      (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (r : EinsteinRelation.External.GantertSection7Support.GantertFixedEnvironmentRealization
        hd Λ hΛ ω hω lam h0 h1) (I : Finset ℝ≥0),
      r.pathLaw.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
        MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
          (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I)
    (h1 : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt_phys)
    (h2 : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (h3 : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (h4 : node_app_u3A_regen_u2D_tailsStmt_phys)
    (h5 : node_app_u3A_factorization_u23_slicesStmt_phys)
    (h6 : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys) :
    node_app_u3A_factorization_u23_independenceStmtV2_phys := by
  exact c7_s3_independence_of_all_start_recenter_phys
    (c6_s3_all_start_recenter_of_requested_identification_phys
      requested_s3_supplied_gantert_c0_fdd) h1 h2 h3 h4 h5 h6

/-- The physical-kernel version of
`EinsteinFull.Blueprint.node_app_u3A_factorization_u23_independence_of_deps`. -/
theorem node_app_u3A_factorization_u23_independence_of_deps_phys
    (h1 : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt_phys)
    (h2 : node_app_u3A_factorization_u23_past_u2D_kernelStmt_phys)
    (h3 : node_app_u3A_factorization_u23_future_u2D_kernelStmt_phys)
    (h4 : node_app_u3A_regen_u2D_tailsStmt_phys)
    (h5 : node_app_u3A_factorization_u23_slicesStmt_phys)
    (h6 : node_app_u3A_factorization_u23_coupling_u2D_scopeStmt_phys) :
    node_app_u3A_factorization_u23_independenceStmtV2_phys := by
  apply c7_s3_independence_of_requested_identification_phys _ h1 h2 h3 h4 h5 h6
  intro d hd Λ hΛ ω hω lam h0 h1 r I
  exact EinsteinFull.u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam Λ hΛ hω h0 h1 r I

end EinsteinFull.Blueprint
