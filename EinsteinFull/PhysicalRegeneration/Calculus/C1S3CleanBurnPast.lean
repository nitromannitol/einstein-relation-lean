import EinsteinFull.Calculus.C1S3CleanBurnPast
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS1PastFiniteHistory
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5CouplingAnalyticRecenter
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5EndpointAverageTransport
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS5Independence
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.SbxS9CouplingAlgebraRecenter
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_endpoint_u2D_disintegration
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_future_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.C19S3CleanActualCovariance
import EinsteinFull.PhysicalRegeneration.Calculus.C19S3CleanScopeHelpers
import EinsteinFull.PhysicalRegeneration.Calculus.C2S3BurnPastLocality
import EinsteinFull.PhysicalRegeneration.Calculus.C2S3PastAssembly
import EinsteinFull.PhysicalRegeneration.Calculus.C6S3SuppliedPathRecenter
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.CoupledEnvironmentRegularity
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Calculus.C1S3CleanBurnPast`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinRelation.Regeneration Classical
/-- The physical-kernel version of
`EinsteinFull.Blueprint.c1_s3_clean_burn_past_of_literal_past_kernel`. -/
theorem c1_s3_clean_burn_past_of_literal_past_kernel_phys (hPastKernel :
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → r₀ < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (_hK : IsRegenerationCouplingPhys hd Q lam l δ h₀.le h₁ P K),
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    ∀ (m : ℕ) (v : ℝ) (H : Regeneration.CoupledSample d → ℝ),
      Measurable[Regeneration.finiteHistorySigma Δ m] H →
      Regeneration.BoundedRealTest H →
      (∀ z, (¬ ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → z.1 t i ≤ v) → H z = 0) →
      ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ v + 3 * R}] A ∧
        (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q.measure] A) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : (∀ᵐ p ∂((volume : Measure (Vec d)).prod Q.measure),
      (K p).map (recenterSample p.1) = K (0, translate p.1 p.2)) ∧
    ∃ η : ℝ, 0 < η ∧ η ≤ 1 ∧
      (∀ᵐ y ∂(volume : Measure (Vec d)), η ≤ ∫ ω,
        ∫ z, killedFutureTest (l / lam) (Renewal.forceCoord hd) (fun _ => (1 : ℝ))
          ((y, ω), z) ∂K (y, ω) ∂Q.measure) ∧
    ∀ m J N k : ℕ,
      ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x (Regeneration.Renewal.forceCoord hd) ≤
          y (Regeneration.Renewal.forceCoord hd) - 4 * (l / lam)}] A ∧
        (fun ω => ∫ z, ((couplingScopeTrialBurnPrebridge (Regeneration.Renewal.regenDelta lam)
          lam (l / lam) m (Regeneration.Renewal.forceCoord hd) J N k).indicator (fun _ => (1 : ℝ))) z *
          (if y ∈ Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd) (l / lam)
            (z.1 (((m + k : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam)) then 1 else 0)
          ∂K (0, ω)) =ᵐ[Q.measure] A  := by
  refine ⟨c19_clean_actual_coupled_covariance_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK, ?_⟩
  obtain ⟨η, hη, hη1, hmean⟩ :=
    c2_s3_actual_positive_future_mean_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  refine ⟨η, hη, hη1, ?_, ?_⟩
  · filter_upwards [hmean] with y hy
    exact le_of_eq hy.symm
  intro m J N k
  apply Filter.Eventually.of_forall
  intro y
  let H : CoupledSample d → ℝ := fun _ => 1
  have hH : Measurable[finiteHistorySigma (Renewal.regenDelta lam) (m + k)] H := measurable_const
  have hbH : BoundedRealTest H := ⟨1, by intro z; simp [H]⟩
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  let E : Set (CoupledSample d) := {z | y ∈ endpointBall i R (z.1 (((m + k : ℕ) : ℝ≥0) * Δ))}
  let G := (couplingScopeTrialBurnPrebridge Δ lam R m i J N k).indicator H
  let F := E.indicator G
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  have hR : 0 < R := div_pos hl h0
  have hF : Measurable[finiteHistorySigma Δ (m + k)] F :=
    (hH.indicator (c1_s3_measurableSet_trial_burn_prebridge_finiteHistory
      Δ hΔ lam R h0 hR m i J N k)).indicator
      (measurableSet_endpointBall_past Δ R i (m + k) y)
  have hbF : BoundedRealTest F := by
    obtain ⟨C, hC⟩ := hbH
    refine ⟨max C 0, fun z => ?_⟩
    by_cases hz : z ∈ E
    · by_cases hΓ : z ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k
      · simpa only [F, G, Set.indicator_of_mem hz, Set.indicator_of_mem hΓ] using
          (hC z).trans (le_max_left C 0)
      · simpa only [F, G, Set.indicator_of_mem hz, Set.indicator_of_notMem hΓ, abs_zero] using
          (le_max_right C 0)
    · simpa only [F, Set.indicator_of_notMem hz, abs_zero] using (le_max_right C 0)
  have hbar : ∀ z, (¬ ∀ t : ℝ≥0, t ≤ ((m + k : ℕ) : ℝ≥0) * Δ → z.1 t i ≤ y i - 7 * R) → F z = 0 := by
    intro z hz
    by_contra hn
    have he : z ∈ E := by
      by_contra h
      exact hn (Set.indicator_of_notMem h _)
    have hΓ : z ∈ couplingScopeTrialBurnPrebridge Δ lam R m i J N k := by
      by_contra h
      exact hn (by simp [F, G, he, h])
    apply hz
    intro t ht
    have hp := c2_s3_burn_prebridge_prefix_support Δ hΔ lam R h0 hR m i J N k z hΓ t ht
    have hball : euclideanNorm (y - (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) + (9 * R) • unitVector i)) < R := he
    have hcoord := coordinate_abs_le_euclideanNorm (y - (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) + (9 * R) • unitVector i)) i
    have habs := (abs_lt.mp (lt_of_le_of_lt hcoord hball)).1
    have hshift : (y - (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) + (9 * R) • unitVector i)) i = y i - (z.1 (((m + k : ℕ) : ℝ≥0) * Δ) i + 9 * R) := by simp [unitVector]
    linarith
  obtain ⟨A, hA, hAo⟩ := hPastKernel d hd Λ₀ r₀ Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK (m+k) (y i - 7*R) F hF hbF hbar
  have hv : y i - 7 * R + 3 * R = y i - 4 * R := by ring
  rw [hv] at hA
  refine ⟨A, hA, ?_⟩
  filter_upwards [hAo] with ω hω
  rw [← hω]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  change G z * (if z ∈ E then 1 else 0) = F z
  by_cases hz : z ∈ E <;> simp [F, hz]

end EinsteinFull.Blueprint
