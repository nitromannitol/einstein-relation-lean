import EinsteinFull.Calculus.SbxS1AllScaleTrialR02
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS1PastFiniteHistory
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS10BridgeIntegrability
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS1SplitGridFreshBits
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5CouplingAnalyticRecenter
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5EndpointAverageTransport
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5Independence
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS9CouplingAlgebraRecenter
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_endpoint_u2D_disintegration
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3ActualPastKernel
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3CleanQuenchedStoppedTube
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3StoppedTubeProducer
import EinsteinFull.PhysicalRegeneration.Calculus.C14S3BurnContraction
import EinsteinFull.PhysicalRegeneration.Calculus.C19S3CleanActualCovariance
import EinsteinFull.PhysicalRegeneration.Calculus.C19S3CleanHistoryParameterIntegral
import EinsteinFull.PhysicalRegeneration.Calculus.C19S3CleanScopeHelpers
import EinsteinFull.PhysicalRegeneration.Calculus.C1S3CleanBurnPast
import EinsteinFull.PhysicalRegeneration.Calculus.C1S3HistoryParameterIntegral
import EinsteinFull.PhysicalRegeneration.Calculus.C2S3BurnPastLocality
import EinsteinFull.PhysicalRegeneration.Calculus.C2S3PastAssembly
import EinsteinFull.PhysicalRegeneration.Calculus.C6S3OneScaleCouplingFactory
import EinsteinFull.PhysicalRegeneration.Calculus.C6S3SuppliedPathRecenter
import EinsteinFull.PhysicalRegeneration.Calculus.C7S3CleanScopeAssembly
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS1CouplingAssemblyR02
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Calculus.SunaS2RationalStoppedLaw
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Regeneration.SbxS1JointSplitR01
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.CoupledEnvironmentRegularity
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.SbxS1AllScaleTrialR02`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration
/-- The physical-kernel version of `EinsteinFull.Blueprint.s1_transfer_supplied_path_event`. -/
theorem s1_transfer_supplied_path_event_phys {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P P' : QuenchedPathLaws d) (K K' : CoupledQuenchedLaws d)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P)
    (hP' : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P')
    (hK : HasProbabilityLaws Q.measure K) (hK' : HasProbabilityLaws Q.measure K')
    (hM : HasPathMarginals Q.measure K P) (hM' : HasPathMarginals Q.measure K' P')
    (A : Set (Path d)) (hA : MeasurableSet A)
    (h : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, q.2.1 ∈ A) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K', q.2.1 ∈ A := by
  have heq := EinsteinFull.s6_supplied_reduced_kernel_pathLaw_unique_phys hd Q lam h0 h1 P P' hP hP'
  have hf := ae_quenched_of_annealed Q.measure K hK h
  have hp : ∀ᵐ ω ∂Q.measure, ∀ᵐ x ∂P' (0, ω), x ∈ A := by
    filter_upwards [hf, hM.1, heq] with ω hfω hmap he
    rw [← he 0, ← hmap]
    exact (ae_map_iff measurable_fst.aemeasurable hA).2 hfω
  apply Measure.ae_compProd_of_ae_ae (hA.preimage measurable_snd.fst)
  filter_upwards [hp, hK'.1, hM'.1] with ω hpω hprob hmap
  let : IsProbabilityMeasure (originCoupledLaw K' ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K') ω]
  apply ae_of_ae_map measurable_fst.aemeasurable
  change ∀ᵐ y ∂(K' (0, ω)).map Prod.fst, y ∈ A
  rwa [hmap]

/-- The physical-kernel version of
`EinsteinFull.Blueprint.s1_transfer_uniform_quenched_path_lower_bound`. -/
theorem s1_transfer_uniform_quenched_path_lower_bound_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P P' : QuenchedPathLaws d)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P)
    (hP' : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P')
    (A : Vec d → Set (Path d)) (ε : ℝ≥0∞)
    (hbound : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, ε ≤ P' (x, ω) (A x)) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, ε ≤ P (x, ω) (A x) := by
  filter_upwards [EinsteinFull.s6_supplied_reduced_kernel_pathLaw_unique_phys
    hd Q lam h0 h1 P P' hP hP', hbound] with ω heq hω
  intro x
  rw [heq x]
  exact hω x

attribute [local instance 2000] EinsteinRelation.instMeasurableSpaceMat
end EinsteinFull.Blueprint
