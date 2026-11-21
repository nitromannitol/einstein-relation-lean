import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinRelation.Regeneration.FirstRegenerationSliceFubini`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinRelation.Regeneration
/-- The physical-kernel version of
`EinsteinRelation.Regeneration.firstRegeneration_slice_integral_eq`. -/
theorem firstRegeneration_slice_integral_eq_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : EinsteinFull.Regeneration.IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (hRestart : HasDeterministicRestart Q.measure Δ K)
    (hUniform : HasUniformSuccessfulEndpoint Q.measure Δ δ R i K)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hb : BoundedRealTest Φ)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B)
    (hBp : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
      B xω = ∫ z, killedFutureTest R i Φ (xω, z) ∂K xω)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hbH : BoundedRealTest H) :
    (∫ p in {p : FieldPair d × CoupledSample d | firstRegenerationTime Δ lam R p.2 i =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
      H p.2 * Φ (iteratedRecord Δ lam R i 1 p) ∂annealedCoupledLaw Q.measure K) =
      (δ / (volume (endpointBall i R (0 : Vec d))).toReal) *
        ∫ y, ∫ ω, firstSlicePastIntegral Δ lam R i m K H (y, ω) * B (y, ω) ∂Q.measure := by
  let G := (forcedBitTrialEvent Δ lam R i m).indicator H
  have hG : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance G :=
    hH.indicator (measurableSet_forcedBitTrialEvent_finiteHistory Δ hΔ lam R hR i m)
  have hbG : BoundedRealTest G := by
    obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ forcedBitTrialEvent Δ lam R i m
    · simpa only [G, Set.indicator_of_mem hz] using (hC z).trans (le_max_left C 0)
    · simpa only [G, Set.indicator_of_notMem hz, abs_zero] using (le_max_right C 0)
  have hsm : MeasurableSet {p : FieldPair d × CoupledSample d |
      firstRegenerationTime Δ lam R p.2 i =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} :=
    ((measurable_firstRegenerationTime Δ lam R i).comp measurable_snd)
      (measurableSet_singleton _)
  rw [← integral_indicator hsm]
  simp_rw [firstRegeneration_slice_integrand Δ hΔ lam R i m H Φ]
  rw [integral_annealed_future_eq_uniformEndpointAverage_phys hd Q lam h0 h1 P K hK hpath hP
    Δ hΔ δ R i hRestart hUniform m G hG hbG (killedFutureTest R i Φ)
    (measurable_killedFutureTest R i Φ hΦ) (boundedRealTest_killedFutureTest R i Φ hb)
    B hB hbB hBp, integral_const_mul,
    integral_annealed_endpointAverage_fubini Q.measure K hK Δ m i R hR G
      (hG.mono (Probability.finiteHistorySigma_le Δ m) le_rfl) hbG B hB hbB]
  simp only [firstSlicePastIntegral, G, div_eq_mul_inv, mul_assoc]

end EinsteinRelation.Regeneration
