import EinsteinFull.Regeneration.GMPUniformExitMinorization
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS10BridgeIntegrability
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCouplingSetwiseLowerR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS1CouplingAssemblyR02
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Regeneration.SbxS1JointSplitR01
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.GMPUniformExitMinorization`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of
`EinsteinFull.Regeneration.uniform_regular_gmp_source_minorization`. -/
theorem uniform_regular_gmp_source_minorization_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) ω)
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) ω
          hω μ hμ.le hμ1),
        HasSourceMinorization (fun x => G.pathLaw x) (Renewal.regenDelta μ)
          δ (l / μ) (Renewal.forceCoord hd) := by
  obtain ⟨a, ha, hstep⟩ := b_coupling_local_steps_phys d hd Λ r l hl
  obtain ⟨c, hc, hchain⟩ := b_coupling_setwise_of_local_chain a l ha
    (lt_of_lt_of_le zero_lt_one hl)
  obtain ⟨hδ, hδ1, hminor⟩ := SbxASourceSetwiseDensityR05.source_minorization_of_rescaled_setwise
    (Renewal.forceCoord hd) l c (lt_of_lt_of_le zero_lt_one hl) hc
  refine ⟨SbxS14MinorizationVolumeR03.windowCoinCoefficient (Renewal.forceCoord hd) l c,
    hδ, hδ1, ?_⟩
  intro Q μ hμ hμ1 ω hω G
  apply hminor μ hμ (Renewal.regenDelta μ) (fun x => G.pathLaw x)
  intro x
  exact hchain μ hμ G x (hstep Q μ hμ hμ1 ω hω G x)

end EinsteinFull.Regeneration
