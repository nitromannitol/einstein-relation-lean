import EinsteinFull.Regeneration.GMPUniformSlabEscape
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
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
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPUniformExitMinorization
import EinsteinFull.PhysicalRegeneration.Regeneration.SbxS1JointSplitR01
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.GMPUniformSlabEscape`

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
`EinsteinFull.Regeneration.uniform_regular_gmp_slab_exit_tail`. -/
theorem uniform_regular_gmp_slab_exit_tail_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ n : ℕ, ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
      (ω : FieldPair d)
      (hω : IsRegular (sourceReducedBound Λ) ω)
      (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
        (one_le_sourceReducedBound Q.ellipticity_parameter) ω
        hω μ hμ.le hμ1) (x : Vec d),
      G.pathLaw x {γ : Path d |
        (((n : ℝ≥0) * Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) <
          coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)} ≤
        ENNReal.ofReal (1 / 15 : ℝ) := by
  obtain ⟨δ, hδ, hδ1, hminor⟩ := uniform_regular_gmp_source_minorization_phys d hd Λ r l hl
  obtain ⟨n, hn⟩ := exists_gmp_survival_le δ (1 / 15) hδ hδ1.le (by norm_num)
  refine ⟨n, ?_⟩
  intro Q μ hμ hμ1 ω hω G x
  let i := Renewal.forceCoord hd
  let R := l / μ
  let Δ := Renewal.regenDelta μ
  let U := coordinateSlab i x R
  have hR : 0 < R := div_pos (lt_of_lt_of_le zero_lt_one hl) hμ
  have hstep : ∀ y, G.pathLaw y {γ : Path d |
      ∀ t : ℝ≥0, t ≤ Δ → γ t ∈ U} ≤ ENNReal.ofReal (1 - δ) :=
    gmp_slab_survival_le_of_source_minorization G Δ δ R i hδ hδ1.le hR
      (hminor Q μ hμ hμ1 ω hω G) x
  have hsurv := hn G U (isOpen_coordinateSlab i x R) Δ hstep x
  have hsub : ∀ᵐ γ ∂G.pathLaw x,
      γ ∈ {γ : Path d | (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) < coordinateSlabExit γ i R} →
      γ ∈ {γ : Path d | ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → γ t ∈ U} := by
    filter_upwards [G.pathLaw_starts_at x] with γ hstart hγ t ht
    have ht' : (t : ℝ≥0∞) < coordinateSlabExit γ i R :=
      (ENNReal.coe_le_coe.mpr ht).trans_lt hγ
    have hm := MarkovProcess.ContinuousPath.mem_of_lt_exitTime
      (coordinateSlab i (γ 0) R) γ t ht'
    change γ 0 = x at hstart
    rw [hstart] at hm
    exact hm
  exact (measure_mono_ae hsub).trans hsurv

end EinsteinFull.Regeneration
