import EinsteinFull.Blueprint.G1.Proofs.SbxS2FutureKernel
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Calculus.C9FutureKernelIndicatorLocality
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Blueprint.G1.Proofs.SbxS2FutureKernel`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Diffusion
/-- The physical-kernel version of
`EinsteinFull.Blueprint.sbxS2_stoppedOriginKernel_restrict_of_coupling`. -/
theorem sbxS2_stoppedOriginKernel_restrict_of_coupling_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h₀ h₁ P K)
    (R : ℝ) (hR : 0 < R) (i : Fin d) :
    ∀ᵐ ω ∂Q.measure,
      ((sbxS2StoppedOriginKernel R i K) ω).restrict {z | NoBacktracking R z.1 i} =
        ((Probability.probabilityPart (originCoupledLaw K)) ω).restrict
          {z | NoBacktracking R z.1 i} := by
  classical
  have hD : MeasurableSet {z : CoupledSample d | NoBacktracking R z.1 i} :=
    (measurableSet_NoBacktracking R i).preimage measurable_fst
  filter_upwards [hK.1.1,
    future_locality_ae_starts_at_origin_of_coupling_phys hd Q lam l δ h₀ h₁ P K hK]
    with ω hp hs
  have : IsProbabilityMeasure ((originCoupledLaw K) ω) := hp
  rw [sbxS2StoppedOriginKernel,
    Kernel.map_apply _ (sbxS2_measurable_stopFutureSample R i),
    Probability.probabilityPart_eq_of_isProbabilityMeasure,
    Measure.restrict_map (sbxS2_measurable_stopFutureSample R i) hD]
  have he : (sbxS2StopFutureSample R i) ⁻¹' {z | NoBacktracking R z.1 i} =ᵐ[(originCoupledLaw K) ω]
      {z | NoBacktracking R z.1 i} := by
    filter_upwards [hs] with z hz
    simpa only [Set.mem_preimage, Set.mem_ofPred_eq, sbxS2StopFutureSample,
      hz, Pi.zero_apply, zero_sub, neg_mul] using
        propext (future_locality_noBacktracking_stopped_iff R hR i z.1)
  rw [Measure.restrict_congr_set he]
  calc
    _ = ((originCoupledLaw K ω).restrict {z | NoBacktracking R z.1 i}).map id := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hD, ae_restrict_of_ae hs] with z hz hstart
      apply Prod.ext
      · simpa only [sbxS2StopFutureSample, id_eq, hstart, Pi.zero_apply, zero_sub, neg_mul]
          using future_locality_stoppedPath_eq_of_noBacktracking R hR i z.1 hz
      · rfl
    _ = _ := Measure.map_id

end EinsteinFull.Blueprint
