import EinsteinFull.Regeneration.NoReturnFromPositiveExit
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
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPBackwardFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPForwardFromPositiveExit
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
`EinsteinFull.Regeneration.NoReturnFromPositiveExit`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory EinsteinRelation
open EinsteinRelation.Regeneration EinsteinRelation.Diffusion
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
/-- The physical-kernel version of
`EinsteinFull.Regeneration.uniform_no_backtracking_of_positive_slab_exit`. -/
theorem uniform_no_backtracking_of_positive_slab_exit_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ) (hL : 1 ≤ L) :
    ∃ l₀ : ℝ, 0 < l₀ ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (P : QuenchedPathLaws d),
        EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q μ hμ.le hμ1 P →
        (∀ᵐ ω ∂Q.measure, ∀ y : Vec d, (2 / 3 : ℝ) ≤ (P (y, ω)).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ}) →
        ∀ᵐ ω ∂Q.measure, ∀ (l : ℝ), l₀ ≤ l → ∀ x : Vec d,
          ENNReal.ofReal (1 / 2 : ℝ) ≤
            P (x, ω) {γ | NoBacktracking (l / μ) γ (Renewal.forceCoord hd)} := by
  obtain ⟨κ, C, hκ, hC, hback⟩ := uniform_supplied_backward_hitting_of_positive_exit_phys d hd Λ r L hL
  let l₀ : ℝ := max 1 (2 * C / κ)
  have hl₀ : 0 < l₀ := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  refine ⟨l₀, hl₀, ?_⟩
  intro Q μ hμ hμ1 P hP hpositive
  filter_upwards [hP, hback Q μ hμ hμ1 P hP hpositive] with ω hω hb
  obtain ⟨hω, G, hrow⟩ := hω
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  intro l hl x
  have hlbound : 2 * C ≤ κ * l := by
    have h := (div_le_iff₀ hκ).mp ((le_max_right 1 (2 * C / κ)).trans hl)
    nlinarith
  have hexp : C * Real.exp (-κ * l) ≤ (1 / 2 : ℝ) := by
    have he := Real.add_one_le_exp (κ * l)
    have hpos : 0 < Real.exp (κ * l) := Real.exp_pos _
    rw [show -κ * l = -(κ * l) by ring, Real.exp_neg]
    rw [← div_eq_mul_inv, div_le_iff₀ hpos]
    nlinarith
  have hcross : P (x, ω) {γ |
      firstHittingBelow γ (Renewal.forceCoord hd) (-(l / μ)) ≠ ⊤} ≤
        ENNReal.ofReal (1 / 2 : ℝ) := by
    calc
      _ ≤ ENNReal.ofReal (C * Real.exp (-κ * μ * (l / μ))) := hb x _
      _ = ENNReal.ofReal (C * Real.exp (-κ * l)) := by congr 2; field_simp
      _ ≤ _ := ENNReal.ofReal_le_ofReal hexp
  have : IsProbabilityMeasure (P (x, ω)) := by rw [hrow x]; infer_instance
  let E : Set (Path d) := {γ | NoBacktracking (l / μ) γ (Renewal.forceCoord hd)}
  have hE : MeasurableSet E := measurableSet_NoBacktracking _ _
  have hhalf : ENNReal.ofReal (1 / 2 : ℝ) = (1 : ℝ≥0∞) / 2 := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num), ENNReal.ofReal_one]
    norm_num
  have hcross' : P (x, ω) Eᶜ ≤ (1 : ℝ≥0∞) / 2 := by
    simpa only [E, NoBacktracking, Set.compl_ofPred, not_not, ← hhalf] using hcross
  have hsum : P (x, ω) E + P (x, ω) Eᶜ = 1 := by
    simpa using measure_add_measure_compl (μ := P (x, ω)) hE
  have hle : (1 : ℝ≥0∞) ≤ P (x, ω) E + (1 : ℝ≥0∞) / 2 := by
    calc
      1 = P (x, ω) E + P (x, ω) Eᶜ := hsum.symm
      _ ≤ P (x, ω) E + (1 : ℝ≥0∞) / 2 := add_le_add_right hcross' _
  rw [hhalf]
  apply ENNReal.le_of_add_le_add_right (by simp : (1 : ℝ≥0∞) / 2 ≠ ⊤)
  exact (ENNReal.add_halves 1).le.trans hle

end EinsteinFull.Regeneration
