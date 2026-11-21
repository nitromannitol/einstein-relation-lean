import EinsteinFull.Regeneration.GMPBackwardFromPositiveExit
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
`EinsteinFull.Regeneration.GMPBackwardFromPositiveExit`

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
`EinsteinFull.Regeneration.uniform_regular_positive_capped_exit`. -/
theorem uniform_regular_positive_capped_exit_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ g : ℝ, 0 < g ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) ω)
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) ω
          hω μ hμ.le hμ1),
        (∀ y : Vec d, (2 / 3 : ℝ) ≤ (G.pathLaw y).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ}) →
        ∀ y : Vec d, (3 / 5 : ℝ) ≤ (G.pathLaw y).real {γ |
          cappedSlabIncrement γ (Renewal.forceCoord hd) (l / μ)
            (Real.toNNReal (g / μ ^ 2)) 0 = 1} := by
  obtain ⟨n, hn⟩ := uniform_regular_gmp_slab_exit_tail_phys d hd Λ r l hl
  let g : ℝ := n + 1
  have hg : 0 < g := by dsimp [g]; positivity
  refine ⟨g, hg, ?_⟩
  intro Q μ hμ hμ1 ω hω G hpositive y
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  have hcap : Real.toNNReal (g / μ ^ 2) =
      ((n + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta μ := by
    apply NNReal.coe_injective
    simp only [Real.coe_toNNReal _ (div_nonneg hg.le (sq_nonneg μ)), NNReal.coe_mul,
      NNReal.coe_natCast, Renewal.regenDelta,
      Real.coe_toNNReal _ (inv_nonneg.mpr (sq_nonneg μ))]
    dsimp [g]
    push_cast
    ring
  have hsub : {γ : Path d |
      (Real.toNNReal (g / μ ^ 2) : ℝ≥0∞) <
        coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)} ⊆
      {γ : Path d | (((n : ℝ≥0) * Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) <
        coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)} := by
    intro γ hγ
    rw [hcap] at hγ
    apply (show (((n : ℝ≥0) * Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) ≤
      ((((n + 1 : ℕ) : ℝ≥0) * Renewal.regenDelta μ : ℝ≥0) : ℝ≥0∞) from by
        exact ENNReal.coe_le_coe.mpr (mul_le_mul_left (by exact_mod_cast Nat.le_succ n) _)).trans_lt hγ
  have hbound := (measure_mono hsub).trans (hn Q μ hμ hμ1 ω hω G y)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
  have hlate : (G.pathLaw y).real {γ |
      (Real.toNNReal (g / μ ^ 2) : ℝ≥0∞) <
        coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)} ≤ (1 / 15 : ℝ) := by
    simpa only [measureReal_def, ENNReal.toReal_ofReal (by norm_num : (0 : ℝ) ≤ 1 / 15)] using hreal
  exact cappedSlab_positive_probability_of_exit_bounds (G.pathLaw y) (Renewal.forceCoord hd)
    (l / μ) (div_pos (by linarith) hμ) _ (hpositive y) hlate

/-- The physical-kernel version of
`EinsteinFull.Regeneration.uniform_regular_backward_hitting_of_positive_exit`. -/
theorem uniform_regular_backward_hitting_of_positive_exit_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (ω : FieldPair d)
        (hω : IsRegular (sourceReducedBound Λ) ω)
        (G : GantertFixedEnvironmentRealization hd (sourceReducedBound Λ)
          (one_le_sourceReducedBound Q.ellipticity_parameter) ω
          hω μ hμ.le hμ1),
        (∀ y : Vec d, (2 / 3 : ℝ) ≤ (G.pathLaw y).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ}) →
        ∀ (x : Vec d) (u : ℝ),
          G.pathLaw x {γ | firstHittingBelow γ (Renewal.forceCoord hd) (-u) ≠ ⊤} ≤
            ENNReal.ofReal (C * Real.exp (-κ * μ * u)) := by
  obtain ⟨g, hg, hcapped⟩ := uniform_regular_positive_capped_exit_phys d hd Λ r l hl
  obtain ⟨κ, C, hκ, hC, hback⟩ :=
    backward_hitting_le_of_regular_positive_capped_exit l (by linarith)
  refine ⟨κ, C, hκ, hC, ?_⟩
  intro Q μ hμ hμ1 ω hω G hpositive x u
  have : IsMarkovKernel G.pathLaw := G.pathLaw_isMarkovKernel
  exact hback hd ω μ (sourceReducedBound Λ)
    (one_le_sourceReducedBound Q.ellipticity_parameter) hω G.pathLaw
    (foundation_arbitrary_supplied_gmp_canonical_FDD hd (sourceReducedBound Λ)
      (one_le_sourceReducedBound Q.ellipticity_parameter) ω
      hω μ hμ.le hμ1 G) x (Renewal.forceCoord hd) (Real.toNNReal (g / μ ^ 2))
    (Real.toNNReal_pos.mpr (div_pos hg (sq_pos_of_pos hμ))) hμ
    (hcapped Q μ hμ hμ1 ω hω G hpositive) u

/-- The physical-kernel version of
`EinsteinFull.Regeneration.uniform_supplied_backward_hitting_of_positive_exit`. -/
theorem uniform_supplied_backward_hitting_of_positive_exit_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r l : ℝ) (hl : 1 ≤ l) :
    ∃ κ C : ℝ, 0 < κ ∧ 0 < C ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (P : QuenchedPathLaws d),
        EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q μ hμ.le hμ1 P →
        (∀ᵐ ω ∂Q.measure, ∀ y : Vec d, (2 / 3 : ℝ) ≤ (P (y, ω)).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ}) →
        ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (u : ℝ),
          P (x, ω) {γ | firstHittingBelow γ (Renewal.forceCoord hd) (-u) ≠ ⊤} ≤
            ENNReal.ofReal (C * Real.exp (-κ * μ * u)) := by
  obtain ⟨κ, C, hκ, hC, hback⟩ := uniform_regular_backward_hitting_of_positive_exit_phys d hd Λ r l hl
  refine ⟨κ, C, hκ, hC, ?_⟩
  intro Q μ hμ hμ1 P hP hpositive
  filter_upwards [hP, hpositive] with ω hω hp
  obtain ⟨hω, G, hrow⟩ := hω
  have hpositiveG : ∀ y : Vec d, (2 / 3 : ℝ) ≤ (G.pathLaw y).real {γ |
      coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ) ≠ ⊤ ∧
      γ (coordinateSlabExit γ (Renewal.forceCoord hd) (l / μ)).toNNReal
        (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = l / μ} := by
    intro y
    rw [← hrow y]
    exact hp y
  intro x u
  rw [hrow x]
  exact hback Q μ hμ hμ1 ω hω G hpositiveG x u

end EinsteinFull.Regeneration
