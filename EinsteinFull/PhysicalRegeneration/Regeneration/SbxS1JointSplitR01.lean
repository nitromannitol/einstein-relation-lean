import EinsteinFull.Regeneration.SbxS1JointSplitR01
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS10BridgeIntegrability
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.SbxS1JointSplitR01`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Regeneration
open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Probability
open EinsteinRelation.External.GantertSection7Support
open EinsteinFull.External.Source.GMP
open EinsteinFull.SbxS10BridgeIntegrability
variable {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d)
  (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (hR : 0 < R)
  (P : QuenchedPathLaws d) [IsMarkovKernel P]
  (hminor : ∀ ω : FieldPair d, HasSourceMinorization (fun x => P (x, ω)) Δ δ R i)
  (hstart : ∀ a, ∀ᵐ γ ∂P a, γ 0 = a.1)
include hstart
/-- The physical-kernel version of `EinsteinFull.Regeneration.s1_canonical_pathMarginal_ae`. -/
theorem s1_canonical_pathMarginal_ae_phys (hd : 2 ≤ d) {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {lam : ℝ} (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h₀ h₁ P) :
    ∀ᵐ ω ∂Q.measure, ∀ x,
      (splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor (x, ω)).map Prod.fst =
        P (x, ω) := by
  filter_upwards [hP] with ω hω
  obtain ⟨_, G, hG⟩ := hω
  intro x
  exact s1_canonical_pathMarginal_of_gmp Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart G hG x

/-- The physical-kernel version of `EinsteinFull.Regeneration.s1_canonical_core_clauses`. -/
theorem s1_canonical_core_clauses_phys (hd : 2 ≤ d) {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {lam : ℝ} (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h₀ h₁ P) :
    let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P ∧
      HasFreshBits Q.measure Δ δ K ∧ HasDeterministicRestart Q.measure Δ K := by
  dsimp only
  have hm := s1_canonical_pathMarginal_ae_phys Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart
    hd Q h₀ h₁ hP
  refine ⟨⟨Filter.Eventually.of_forall (fun _ => inferInstance),
    Filter.Eventually.of_forall (fun _ => inferInstance)⟩, ?_,
    hasFreshBits_splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor Q.measure hstart,
    s1_canonical_hasDeterministicRestart Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart Q.measure⟩
  constructor
  · filter_upwards [hm] with ω hω
    exact hω 0
  · filter_upwards [Measure.quasiMeasurePreserving_snd.ae hm] with a ha
    exact ha a.1

/-- The physical-kernel version of `EinsteinFull.Regeneration.s1_canonical_all_clauses`. -/
theorem s1_canonical_all_clauses_phys (hd : 2 ≤ d) {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) {lam : ℝ} (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h₀ h₁ P) :
    let K := splitContinuousCouplingKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor
    HasProbabilityLaws Q.measure K ∧ HasPathMarginals Q.measure K P ∧
      EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h₀ h₁ P ∧
      HasFreshBits Q.measure Δ δ K ∧ HasDeterministicRestart Q.measure Δ K ∧
      HasSuccessfulBridgeSupport Q.measure Δ i R K ∧
      HasUniformSuccessfulEndpoint Q.measure Δ δ R i K ∧
      Renewal.HasOneIntervalKernel Q.measure Δ δ R i P K := by
  obtain ⟨hp, hm, hf, hr⟩ :=
    s1_canonical_core_clauses_phys Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart hd Q h₀ h₁ hP
  exact ⟨hp, hm, hP, hf, hr,
    s1_canonical_hasSuccessfulBridgeSupport Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart Q.measure,
    s1_canonical_hasUniformSuccessfulEndpoint Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart Q.measure,
    s1_canonical_hasOneIntervalKernel Δ hΔ δ R i hδ₀ hδ₁ hR P hminor hstart Q.measure⟩

end EinsteinFull.Regeneration
