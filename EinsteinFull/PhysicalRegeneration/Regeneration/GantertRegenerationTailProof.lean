import EinsteinFull.Regeneration.GantertRegenerationTailProof
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
import EinsteinFull.PhysicalRegeneration.Regeneration.AnnealedHistoryRestart
import EinsteinFull.PhysicalRegeneration.Regeneration.CandidateConstants
import EinsteinFull.PhysicalRegeneration.Regeneration.CandidateInnerBounds
import EinsteinFull.PhysicalRegeneration.Regeneration.CoupledCandidateMoment
import EinsteinFull.PhysicalRegeneration.Regeneration.FinitenessFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.FirstRegenerationFiniteness
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPBackwardFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPDowncrossingFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPDowncrossingSmallTilt
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPExitExhaustion
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPExitSmoothPayoff
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPForwardFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPGeometricSlabExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPPayoffComparison
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPPositiveSlabExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPScaledSlabExit
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPSlabExitMoment
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPUniformExitMinorization
import EinsteinFull.PhysicalRegeneration.Regeneration.GMPUniformSlabEscape
import EinsteinFull.PhysicalRegeneration.Regeneration.GuardEstimate
import EinsteinFull.PhysicalRegeneration.Regeneration.NoReturnFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedCenteredSurvival
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedWindowMaximum
import EinsteinFull.PhysicalRegeneration.Regeneration.RegenerationEndpointMoment
import EinsteinFull.PhysicalRegeneration.Regeneration.SbxS1JointSplitR01
import EinsteinFull.PhysicalRegeneration.Regeneration.TailFromPositiveExit
import EinsteinFull.PhysicalRegeneration.Regeneration.TrialContraction
import EinsteinFull.PhysicalRegeneration.Regeneration.TrialFailureFactor
import EinsteinFull.PhysicalRegeneration.Regeneration.UniformFirstCandidate
import EinsteinFull.PhysicalRegeneration.Regeneration.UniformReturnAtGrid
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.GantertRegenerationTailProof`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.External
open EinsteinRelation
/-- The physical-kernel version of `EinsteinFull.External.gantert_regeneration_tail_holds`. -/
theorem gantert_regeneration_tail_holds_phys (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K →
      ENNReal.ofReal (1 / 2 : ℝ) ≤
        Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam)) ∧
      ∀ t : ℝ, 0 ≤ t →
        Regeneration.annealedCoupledLaw Q.measure K
          {ωz | ENNReal.ofReal t < regenerationTime hd lam l 1 ωz.2} ≤
            ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t)) := by
  obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
  by_cases hΛ : 1 ≤ Λ₀
  · obtain ⟨L, hL, hpos⟩ := Regeneration.gmp_positive_slab_exit_phys n hd Λ₀ hΛ
    obtain ⟨l₀, hl₀, hsep, hbounds⟩ :=
      Regeneration.first_regeneration_bounds_of_positive_exit_phys (n + 1) hd Λ₀ r₀ L hL
    refine ⟨l₀, hl₀, hsep, fun l hl δ hδ hδ1 => ?_⟩
    obtain ⟨c, C, hc, hC, h⟩ := hbounds l hl δ hδ hδ1
    refine ⟨c, C, hc, hC, fun Q lam h₀ h₁ P K hK => h Q lam h₀ h₁ P K hK ?_⟩
    obtain ⟨-, -, hred, -⟩ := hK
    filter_upwards [hred] with ω hω
    obtain ⟨hω', G, hG⟩ := hω
    intro y
    rw [hG y]
    exact hpos L le_rfl r₀ Q lam h₀ h₁ ω hω' G y
  · obtain ⟨l₀, hl₀, hsep, hbounds⟩ :=
      Regeneration.first_regeneration_bounds_of_positive_exit_phys (n + 1) hd Λ₀ r₀ 1 le_rfl
    refine ⟨l₀, hl₀, hsep, fun l hl δ hδ hδ1 => ?_⟩
    obtain ⟨c, C, hc, hC, -⟩ := hbounds l hl δ hδ hδ1
    exact ⟨c, C, hc, hC, fun Q => absurd Q.ellipticity_parameter hΛ⟩

end EinsteinFull.External
