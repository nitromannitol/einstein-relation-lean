import EinsteinFull.Regeneration.TailFromPositiveExit
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS10BridgeIntegrability
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3StoppedTubeProducer
import EinsteinFull.PhysicalRegeneration.Calculus.C1S3HistoryParameterIntegral
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnClosureR15
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnR13
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCouplingSetwiseLowerR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS1CouplingAssemblyR02
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Regeneration.FinitenessFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.FirstRegenerationFiniteness
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPBackwardFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPForwardFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPUniformExitMinorization
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPUniformSlabEscape
import EinsteinFull.PhysicalRegeneration.Regeneration.GuardEstimate
import EinsteinFull.PhysicalRegeneration.Regeneration.NoReturnFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedCenteredSurvival
import EinsteinFull.PhysicalRegeneration.Regeneration.SbxS1JointSplitR01
import EinsteinFull.PhysicalRegeneration.Regeneration.UniformReturnAtGrid
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.TailFromPositiveExit`

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
`EinsteinFull.Regeneration.first_regeneration_bounds_of_positive_exit_and_moment`. -/
theorem first_regeneration_bounds_of_positive_exit_and_moment_phys
    (d : ℕ) (hd : 2 ≤ d) (Λ r L : ℝ) (hL : 1 ≤ L) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r < 2 * l₀ ∧
      ∀ (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
      ∀ (s D : ℝ), 0 < s → 0 < D →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ (Q : EnvironmentLaw d Λ r) (μ : ℝ) (hμ : 0 < μ) (hμ1 : μ ≤ 1)
        (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
        IsRegenerationCouplingPhys hd Q μ l δ hμ.le hμ1 P K →
        (∀ᵐ ω ∂Q.measure, ∀ y : Vec d, (2 / 3 : ℝ) ≤ (P (y, ω)).real {γ |
          coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ) ≠ ⊤ ∧
          γ (coordinateSlabExit γ (Renewal.forceCoord hd) (L / μ)).toNNReal
            (Renewal.forceCoord hd) - γ 0 (Renewal.forceCoord hd) = L / μ}) →
        Integrable (fun q : FieldPair d × CoupledSample d =>
          Real.exp (s * (μ * (q.2.1 (firstRegenerationTime (Renewal.regenDelta μ)
            μ (l / μ) q.2 (Renewal.forceCoord hd)).toNNReal (Renewal.forceCoord hd) -
              q.2.1 0 (Renewal.forceCoord hd))))) (annealedCoupledLaw Q.measure K) →
        (∫ q : FieldPair d × CoupledSample d,
          Real.exp (s * (μ * (q.2.1 (firstRegenerationTime (Renewal.regenDelta μ)
            μ (l / μ) q.2 (Renewal.forceCoord hd)).toNNReal (Renewal.forceCoord hd) -
              q.2.1 0 (Renewal.forceCoord hd)))) ∂annealedCoupledLaw Q.measure K) ≤ D →
        ENNReal.ofReal (1 / 2 : ℝ) ≤
          annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / μ)) ∧
        ∀ t : ℝ, 0 ≤ t →
          annealedCoupledLaw Q.measure K {q | ENNReal.ofReal t < regenerationTime hd μ l 1 q.2} ≤
            ENNReal.ofReal (C * Real.exp (-c * μ ^ 2 * t)) := by
  obtain ⟨l₁, hl₁, hback⟩ := uniform_no_backtracking_of_positive_slab_exit_phys d hd Λ r L hL
  obtain ⟨l₂, hl₂, hfinite⟩ := first_regeneration_finite_of_positive_slab_exit_phys d hd Λ r L hL
  obtain ⟨g, hg, hforward⟩ := uniform_supplied_forward_hitting_of_positive_exit_phys d hd Λ r L hL
  let l₀ := max (max l₁ l₂) (r + 1)
  have hl₀ : 0 < l₀ := lt_of_lt_of_le hl₁ ((le_max_left _ _).trans (le_max_left _ _))
  have hsep : r < 2 * l₀ := by
    have h := le_max_right (max l₁ l₂) (r + 1)
    linarith
  refine ⟨l₀, hl₀, hsep, ?_⟩
  intro l δ hl hδ0 hδ1 s D hs hD
  let κ : ℝ := 1 / (400 * g)
  let C₀ : ℝ := Real.exp (1 / 200)
  refine ⟨min (κ / 2) (s * κ / 2), C₀ + D * Real.exp (12 * s * l),
    lt_min (by dsimp [κ]; positivity) (by dsimp [κ]; positivity), by dsimp [C₀]; positivity, ?_⟩
  intro Q μ hμ hμ1 P K hK hpositive hint hmoment
  have hl₁' : l₁ ≤ l := ((le_max_left _ _).trans (le_max_left _ _)).trans hl
  have hl₂' : l₂ ≤ l := ((le_max_right _ _).trans (le_max_left _ _)).trans hl
  have hlpos : 0 < l := lt_of_lt_of_le hl₀ hl
  have hsep' : r < 2 * l := by linarith
  have : IsProbabilityMeasure Q.measure := Q.probability
  have hback' : ∀ᵐ ω ∂Q.measure, ∀ x, ENNReal.ofReal (1 / 2 : ℝ) ≤
      P (x, ω) {γ | NoBacktracking (l / μ) γ (Renewal.forceCoord hd)} := by
    filter_upwards [hback Q μ hμ hμ1 P hK.2.2.1 hpositive] with ω hω
    exact hω l hl₁'
  have hhit : ∀ (T : ℝ≥0) (a : ℝ), 0 ≤ a → ∀ᵐ ω ∂Q.measure,
      P (0, ω) {γ | (T : ℝ≥0∞) ≤ firstHittingAbove γ (Renewal.forceCoord hd) a} ≤
        ENNReal.ofReal (C₀ * Real.exp (-κ * μ ^ 2 * T + μ * a)) := by
    intro T a ha
    filter_upwards [hforward Q μ hμ hμ1 P hK.2.2.1 hpositive] with ω hω
    exact hω 0 T a ha
  have hf := hfinite Q μ hμ hμ1 l δ hl₂' hsep' hδ0 hδ1 P K hK hpositive
  refine ⟨no_return_mass_of_quenched hd Q.measure P K hK.1 hK.2.1 (l / μ) _ ?_, ?_⟩
  · filter_upwards [hback'] with ω hω
    exact hω 0
  · intro t ht
    have hEnd := first_regeneration_endpoint_tail_of_exp_moment Q.measure K hK.1
      (Renewal.regenDelta μ) μ (l / μ) (Renewal.forceCoord hd) s D hs.le hint hmoment
    have hHit := annealed_forward_hitting_bound Q.measure P K hK.1 hK.2.1 μ κ C₀
      (Renewal.forceCoord hd) hhit
    have htail := first_regeneration_tail_of_hitting_and_endpoint Q.measure K hK.1
      (Renewal.regenDelta μ) (EinsteinRelation.regenDelta_pos hμ) μ l hμ hlpos
      (Renewal.forceCoord hd) hK.2.2.2.2.2.1 hf κ s C₀ D (by dsimp [κ]; positivity)
      (by dsimp [C₀]; positivity) hD hHit hEnd t.toNNReal
    simpa only [regenerationTime, Regeneration.regenerationTime_one,
      ENNReal.coe_nnreal_eq, Real.coe_toNNReal _ ht] using htail

end EinsteinFull.Regeneration
