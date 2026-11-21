import EinsteinFull.Regeneration.CandidateInnerBounds
import EinsteinFull.Regeneration.PhysicalKernelPredicate
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.PhysicalRegeneration.Blueprint.Foundation.node_app_u3A_regen_u2D_tails
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.Proofs.W2Queue0440
import EinsteinFull.PhysicalRegeneration.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.PhysicalRegeneration.Calculus.C10S3StoppedTubeProducer
import EinsteinFull.PhysicalRegeneration.Calculus.C1S3HistoryParameterIntegral
import EinsteinFull.PhysicalRegeneration.Calculus.SbxAGlobalReducedKernelR04
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnClosureR15
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredLocalReturnR13
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredSurvivalR12
import EinsteinFull.PhysicalRegeneration.Calculus.SbxBCenteredTubeChainR03
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS3JointReducedKernelR01
import EinsteinFull.PhysicalRegeneration.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.PhysicalRegeneration.Frozen.RegenerationCoupling
import EinsteinFull.PhysicalRegeneration.Regeneration.AnnealedHistoryRestart
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedCenteredSurvival
import EinsteinFull.PhysicalRegeneration.Regeneration.ReducedWindowMaximum
import EinsteinFull.PhysicalRegeneration.Regeneration.UniformFirstCandidate
import EinsteinFull.PhysicalRegeneration.Vendor.Diffusion.GMPFamilyAPI
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.DeterministicEndpointNullSets
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.FirstRegenerationSliceFubini
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.KilledFutureConditionalMean
import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.RenewalCarriers

/-!
# Physical-kernel version of
`EinsteinFull.Regeneration.CandidateInnerBounds`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
attribute [local irreducible] firstRoundedCandidate roundedCandidateSequence passageSequence
/-- The physical-kernel version of
`EinsteinFull.Regeneration.ae_grid_endpoint_of_origin_and_product`. -/
theorem ae_grid_endpoint_of_origin_and_product_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (p : Vec d × FieldPair d → Prop)
    (horigin : ∀ᵐ ω ∂Q.measure, p (0, ω))
    (hprod : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure, p xω) (m : ℕ) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K,
      p (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) := by
  by_cases hm : m = 0
  · subst m
    have hs := ae_origin_start_of_isGMPReducedKernel_phys hd Q lam h0.le h1 P K hK.1 hK.2.1 hK.2.2.1
    have hqmp : Measure.QuasiMeasurePreserving
        (Prod.fst : FieldPair d × CoupledSample d → FieldPair d)
        (annealedCoupledLaw Q.measure K) Q.measure := by
      refine ⟨measurable_fst, ?_⟩
      rw [EinsteinFull.Blueprint.c10_s3_annealed_environment_map Q K hK.1]
    filter_upwards [hs, hqmp.ae horigin] with q hq hp
    simpa only [Nat.cast_zero, zero_mul, hq] using hp
  · have hΔ : 0 < Renewal.regenDelta lam := EinsteinRelation.regenDelta_pos h0
    have ht : 0 < (m : ℝ≥0) * Renewal.regenDelta lam :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hΔ
    exact ae_at_endpoint_of_product_ae_phys hd Q lam h0.le h1 P K hK.1 hK.2.1 hK.2.2.1 _ ht _ hprod

/-- The physical-kernel version of `EinsteinFull.Regeneration.inner_first_round_le`. -/
theorem inner_first_round_le_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (R b D : ℝ) (i : Fin d)
    (hP1 : ∀ᵐ ω ∂Q.measure, ∀ (x : Vec d) (L : ℝ), 0 ≤ L →
      ∫⁻ γ, firstCandidateWeight (Renewal.regenDelta lam) lam R L b i γ ∂P (x, ω) ≤
        ENNReal.ofReal D) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (m : ℕ) (L : ℝ), 0 ≤ L →
      ∫⁻ w, failedRoundWeight (Renewal.regenDelta lam) lam R L b i 0 w
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal D := by
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.fst : FieldPair d × CoupledSample d → FieldPair d)
      (annealedCoupledLaw Q.measure K) Q.measure := by
    refine ⟨measurable_fst, ?_⟩
    rw [EinsteinFull.Blueprint.c10_s3_annealed_environment_map Q K hK.1]
  rw [ae_all_iff]
  intro m
  filter_upwards [EinsteinFull.Blueprint.c10_s3_grid_endpoint_path_marginal_phys hd Q lam h0 h1 l δ
    P K hK m, hqmp.ae hP1] with q hmarg hb
  intro L hL
  simp only [failedRoundWeight_zero]
  have hmeas : Measurable (fun γ : Path d =>
      firstCandidateWeight (Renewal.regenDelta lam) lam R L b i γ) :=
    (measurable_firstCandidateWeight (Renewal.regenDelta lam) lam R b i).comp
      (measurable_const.prodMk measurable_id)
  calc ∫⁻ w, firstCandidateWeight (Renewal.regenDelta lam) lam R L b i w.1
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1)
      = ∫⁻ γ, firstCandidateWeight (Renewal.regenDelta lam) lam R L b i γ
        ∂(K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1)).map Prod.fst :=
        (lintegral_map hmeas measurable_fst).symm
    _ = ∫⁻ γ, firstCandidateWeight (Renewal.regenDelta lam) lam R L b i γ
        ∂P (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) := by rw [hmarg]
    _ ≤ ENNReal.ofReal D := hb _ L hL

/-- The physical-kernel version of `EinsteinFull.Regeneration.inner_failed_coin_le`. -/
theorem inner_failed_coin_le_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (R b E : ℝ) (i : Fin d)
    (hP2 : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      ∫⁻ γ, squaredRestartWeight (Renewal.regenDelta lam) lam R b i γ ∂P (x, ω) ≤
        ENNReal.ofReal E) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      ∫⁻ v, failedCoinWeight (Renewal.regenDelta lam) lam R b i v
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤
        ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (1 - δ) + ENNReal.ofReal E) := by
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.fst : FieldPair d × CoupledSample d → FieldPair d)
      (annealedCoupledLaw Q.measure K) Q.measure := by
    refine ⟨measurable_fst, ?_⟩
    rw [EinsteinFull.Blueprint.c10_s3_annealed_environment_map Q K hK.1]
  rw [ae_all_iff]
  intro m
  have hgood := ae_grid_endpoint_of_origin_and_product_phys hd Q lam h0 h1 l δ P K hK
    (fun xω => IsProbabilityMeasure (K xω) ∧ FreshBitsAt (Renewal.regenDelta lam) δ K xω)
    (by filter_upwards [hK.1.1, hK.2.2.2.1.1] with ω hp hf using ⟨hp, hf⟩)
    (by filter_upwards [hK.1.2, hK.2.2.2.1.2] with xω hp hf using ⟨hp, hf⟩) m
  filter_upwards [hgood, EinsteinFull.Blueprint.c10_s3_grid_endpoint_path_marginal_phys hd Q lam h0 h1
    l δ P K hK m, hqmp.ae hP2] with q hq hmarg hb
  obtain ⟨hprob, hfresh⟩ := hq
  have hbitm : MeasurableSet {v : CoupledSample d | v.2 0 = false} :=
    measurableSet_eq_fun ((measurable_pi_apply 0).comp measurable_snd) measurable_const
  have hsq : Measurable (squaredRestartWeight (d := d) (Renewal.regenDelta lam) lam R b i) :=
    measurable_squaredRestartWeight _ lam R b i
  calc ∫⁻ v, failedCoinWeight (Renewal.regenDelta lam) lam R b i v
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1)
      ≤ ∫⁻ v, ENNReal.ofReal (1 / 2) *
          ({v : CoupledSample d | v.2 0 = false}.indicator 1 v +
            squaredRestartWeight (Renewal.regenDelta lam) lam R b i v.1)
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) :=
        lintegral_mono fun v => failedCoinWeight_le_half _ lam R b i v
    _ = ENNReal.ofReal (1 / 2) *
          (K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) {v | v.2 0 = false} +
            ∫⁻ γ, squaredRestartWeight (Renewal.regenDelta lam) lam R b i γ
              ∂P (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1)) := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_add_left (measurable_one.indicator hbitm), lintegral_indicator_one hbitm,
          ← hmarg, lintegral_map hsq measurable_fst]
    _ ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (1 - δ) + ENNReal.ofReal E) := by
        rw [measure_firstBit_false _ δ K _ hfresh]
        gcongr
        exact hb _

end EinsteinFull.Regeneration
