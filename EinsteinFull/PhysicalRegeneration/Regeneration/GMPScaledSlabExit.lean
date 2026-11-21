import EinsteinFull.Regeneration.GMPScaledSlabExit
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
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPGeometricSlabExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPUniformExitMinorization
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPUniformSlabEscape
import EinsteinFull.PhysicalRegeneration.Regeneration.SbxS1JointSplitR01
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.GMPScaledSlabExit`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory Set EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of
`EinsteinFull.Regeneration.uniform_regular_gmp_scaled_slab_exit_geometric`. -/
theorem uniform_regular_gmp_scaled_slab_exit_geometric_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) ω)
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) ω
          hω μ hμ.le hμ1) (c x : Vec d) (U : Set (Vec d))
        (_ : U ⊆ coordinateSlab (Renewal.forceCoord hd) c (l / μ)) (n : ℕ),
      G.pathLaw x {γ : Path d | (n : ℝ) < μ ^ 2 *
        (MarkovProcess.ContinuousPath.exitTime U γ).toReal} ≤
        ENNReal.ofReal (1 - δ) ^ n := by
  obtain ⟨δ, hδ, hδ1, hgeo⟩ := uniform_regular_gmp_slab_exit_geometric_phys d hd Λ r l hl
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro Q μ hμ hμ1 ω hω G c x U hU n
  have hm : 0 < μ ^ 2 := by positivity
  have hΔ : (Renewal.regenDelta μ : ℝ) = (μ ^ 2)⁻¹ := by
    simp [Renewal.regenDelta, Real.toNNReal_of_nonneg (inv_nonneg.mpr hm.le)]
  have hsub : {γ : Path d | (n : ℝ) < μ ^ 2 *
      (MarkovProcess.ContinuousPath.exitTime U γ).toReal} ⊆
      {γ : Path d | (((n : ℝ≥0) * Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) <
        MarkovProcess.ContinuousPath.exitTime
          (coordinateSlab (Renewal.forceCoord hd) c (l / μ)) γ} := by
    intro γ hγ
    change (n : ℝ) < μ ^ 2 * (MarkovProcess.ContinuousPath.exitTime U γ).toReal at hγ
    have hfinite : MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤ := by
      intro ht
      simp only [ht, ENNReal.toReal_top, mul_zero] at hγ
      exact (not_lt_of_ge (Nat.cast_nonneg n)) hγ
    have hreal : (n : ℝ) * (μ ^ 2)⁻¹ <
        (MarkovProcess.ContinuousPath.exitTime U γ).toReal := by
      have h := (div_lt_iff₀ hm).2 (by nlinarith :
        (n : ℝ) < (MarkovProcess.ContinuousPath.exitTime U γ).toReal * μ ^ 2)
      simpa [div_eq_mul_inv] using h
    have hstep : (((n : ℝ≥0) * Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) <
        MarkovProcess.ContinuousPath.exitTime U γ := by
      rw [← ENNReal.ofReal_coe_nnreal]
      apply (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hfinite).2
      simpa only [NNReal.coe_mul, NNReal.coe_natCast, hΔ] using hreal
    exact hstep.trans_le (MarkovProcess.ContinuousPath.exitTime_mono hU γ)
  exact (measure_mono hsub).trans (hgeo Q μ hμ hμ1 ω hω G c x n)

end EinsteinFull.Regeneration
