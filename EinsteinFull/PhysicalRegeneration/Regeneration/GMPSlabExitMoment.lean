import EinsteinFull.Regeneration.GMPSlabExitMoment
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
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPExitExhaustion
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPGeometricSlabExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPScaledSlabExit
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
`EinsteinFull.Regeneration.GMPSlabExitMoment`

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
`EinsteinFull.Regeneration.uniform_regular_gmp_slab_exit_exponential_moment`. -/
theorem uniform_regular_gmp_slab_exit_exponential_moment_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) ω)
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) ω
          hω μ hμ.le hμ1) (c x : Vec d) (U : Set (Vec d)),
        IsOpen U → U ⊆ coordinateSlab (Renewal.forceCoord hd) c (l / μ) →
        (∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤) ∧
        Integrable (fun γ => Real.exp ((δ / 4) * (μ ^ 2 *
          (MarkovProcess.ContinuousPath.exitTime U γ).toReal))) (G.pathLaw x) ∧
        (∫ γ, Real.exp ((δ / 4) * (μ ^ 2 *
          (MarkovProcess.ContinuousPath.exitTime U γ).toReal)) ∂G.pathLaw x) ≤
            Real.exp δ * Real.exp (δ / 4) / (1 - Real.exp (δ / 4 - δ / 2)) := by
  obtain ⟨δ, hδ, hδ1, hgeo⟩ := uniform_regular_gmp_scaled_slab_exit_geometric_phys d hd Λ r l hl
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro Q μ hμ hμ1 ω hω G c x U hU hsub
  let : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hfin : ∀ᵐ γ ∂G.pathLaw x, MarkovProcess.ContinuousPath.exitTime U γ ≠ ⊤ := by
    filter_upwards [gmp_ae_source_slab_exit_ne_top_phys d hd Λ r l hl Q μ hμ hμ1 ω hω G c x] with γ hγ
    exact ne_top_of_le_ne_top hγ (MarkovProcess.ContinuousPath.exitTime_mono hsub γ)
  refine ⟨hfin, ?_⟩
  apply exponential_moment_le_of_geometric_tail (G.pathLaw x)
    (fun γ => μ ^ 2 * (MarkovProcess.ContinuousPath.exitTime U γ).toReal)
  · exact measurable_const.mul ((MarkovProcess.ContinuousPath.measurable_exitTime U hU).ennreal_toReal)
  · intro γ
    exact mul_nonneg (sq_nonneg μ) ENNReal.toReal_nonneg
  · exact hδ
  · exact hδ1
  · exact hgeo Q μ hμ hμ1 ω hω G c x U hsub

/-- The physical-kernel version of
`EinsteinFull.Regeneration.uniform_regular_gmp_slab_exit_mean`. -/
theorem uniform_regular_gmp_slab_exit_mean_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) ω)
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) ω
          hω μ hμ.le hμ1) (c x : Vec d) (U : Set (Vec d)),
        IsOpen U → U ⊆ coordinateSlab (Renewal.forceCoord hd) c (l / μ) →
        Integrable (fun γ => μ ^ 2 *
          (MarkovProcess.ContinuousPath.exitTime U γ).toReal) (G.pathLaw x) ∧
        (∫ γ, μ ^ 2 * (MarkovProcess.ContinuousPath.exitTime U γ).toReal ∂G.pathLaw x) ≤
          (Real.exp δ * Real.exp (δ / 4) / (1 - Real.exp (δ / 4 - δ / 2))) / (δ / 4) := by
  obtain ⟨δ, hδ, hδ1, hmoment⟩ := uniform_regular_gmp_slab_exit_exponential_moment_phys d hd Λ r l hl
  refine ⟨δ, hδ, hδ1, ?_⟩
  intro Q μ hμ hμ1 ω hω G c x U hU hsub
  obtain ⟨_, hexp, hbound⟩ := hmoment Q μ hμ hμ1 ω hω G c x U hU hsub
  let S : Path d → ℝ := fun γ => μ ^ 2 * (MarkovProcess.ContinuousPath.exitTime U γ).toReal
  have hS : Measurable S :=
    measurable_const.mul ((MarkovProcess.ContinuousPath.measurable_exitTime U hU).ennreal_toReal)
  have hS0 : ∀ γ, 0 ≤ S γ := fun _ => mul_nonneg (sq_nonneg μ) ENNReal.toReal_nonneg
  have ha : 0 < δ / 4 := by positivity
  have hpoint : ∀ γ, S γ ≤ Real.exp ((δ / 4) * S γ) / (δ / 4) := by
    intro γ
    apply (le_div_iff₀ ha).2
    have h := Real.add_one_le_exp ((δ / 4) * S γ)
    nlinarith
  have hSi : Integrable S (G.pathLaw x) := by
    apply (hexp.div_const (δ / 4)).mono' hS.aestronglyMeasurable
    filter_upwards with γ
    rw [Real.norm_eq_abs, abs_of_nonneg (hS0 γ)]
    exact hpoint γ
  refine ⟨hSi, ?_⟩
  calc
    (∫ γ, S γ ∂G.pathLaw x) ≤
        ∫ γ, Real.exp ((δ / 4) * S γ) / (δ / 4) ∂G.pathLaw x :=
      integral_mono_ae hSi (hexp.div_const _) (Filter.Eventually.of_forall hpoint)
    _ = (∫ γ, Real.exp ((δ / 4) * S γ) ∂G.pathLaw x) / (δ / 4) := by
      rw [integral_div]
    _ ≤ _ := div_le_div_of_nonneg_right hbound ha.le

end EinsteinFull.Regeneration
