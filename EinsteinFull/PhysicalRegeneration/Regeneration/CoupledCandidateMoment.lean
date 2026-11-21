import EinsteinFull.Regeneration.CoupledCandidateMoment
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
import EinsteinFull.PhysicalRegeneration.Regeneration.CandidateInnerBounds
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
`EinsteinFull.Regeneration.CoupledCandidateMoment`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
attribute [local irreducible] firstRoundedCandidate roundedCandidateSequence passageSequence
  firstSuccessfulCandidate
/-- The physical-kernel version of `EinsteinFull.Regeneration.lintegral_roundHistoryWeight_le`. -/
theorem lintegral_roundHistoryWeight_le_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (R b D ρ : ℝ) (hR : 0 < R) (i : Fin d)
    (h1st : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (m : ℕ) (L : ℝ), 0 ≤ L →
      ∫⁻ w, failedRoundWeight (Renewal.regenDelta lam) lam R L b i 0 w
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal D)
    (hcoin : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      ∫⁻ v, failedCoinWeight (Renewal.regenDelta lam) lam R b i v
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal ρ)
    (T₀ : CoupledSample d → ℝ≥0∞) (hT₀ : Measurable T₀)
    (hgrid₀ : ∀ z, T₀ z ≠ ⊤ → ∃ m : ℕ,
      T₀ z = (((m : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞))
    (W₀ : CoupledSample d → ℝ≥0∞) (hW₀ : Measurable W₀)
    (L₀ : CoupledSample d → ℝ) (hL₀m : Measurable L₀) (hL₀ : ∀ z, 0 ≤ L₀ z)
    (hdec₀ : HistoryDecided (Renewal.regenDelta lam) T₀ (fun z => (W₀ z, L₀ z))) (N : ℕ) :
    ∫⁻ q, roundHistoryWeight (Renewal.regenDelta lam) lam R b i T₀ W₀ L₀ N q.2
        ∂annealedCoupledLaw Q.measure K ≤
      ENNReal.ofReal ρ ^ N * ENNReal.ofReal D *
        ∫⁻ q, {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2) q
          ∂annealedCoupledLaw Q.measure K := by
  let Δ := Renewal.regenDelta lam
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  induction N with
  | zero =>
    have h := lintegral_grid_stopping_le_of_decided_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
      T₀ hT₀ hgrid₀ W₀ hW₀
      (fun p => failedRoundWeight Δ lam R (L₀ p.1) b i 0 p.2)
      ((measurable_failedRoundWeight_joint Δ lam R b i 0).comp
        ((hL₀m.comp measurable_fst).prodMk measurable_snd))
      (by
        intro m z z' hag hz
        obtain ⟨hT, hWL⟩ := hdec₀ m z z' hag hz
        simp only [Prod.mk.injEq] at hWL
        refine ⟨hT, ?_⟩
        simp only [hWL.1, hWL.2])
      (ENNReal.ofReal D)
      (by
        filter_upwards [h1st] with q hq m _
        exact hq m (L₀ q.2) (hL₀ q.2))
    simp only [pow_zero, one_mul]
    exact h
  | succ N ih =>
    let TN := roundTime Δ lam R i T₀ L₀ N
    let WN := roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N
    have hTN : Measurable TN := measurable_roundTime Δ lam R i T₀ hT₀ L₀ hL₀m N
    have hWN : Measurable WN := measurable_roundHistoryWeight Δ lam R b i T₀ hT₀ W₀ hW₀ L₀ hL₀m N
    have hgridN : ∀ z, TN z ≠ ⊤ → ∃ m : ℕ, TN z = (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
      intro z hz
      have hT₀z : T₀ z ≠ ⊤ := by
        intro htop
        apply hz
        simp only [TN, roundTime, ite_eq_left htop]
      obtain ⟨k, hk⟩ := hgrid₀ z hT₀z
      have hRT : TN z = T₀ z + roundedCandidateSequence Δ lam R (L₀ z)
          (sampleTimeShift Δ z (T₀ z).toNNReal) i N := by
        simp only [TN, roundTime, ite_eq_right hT₀z]
      have hCfin : roundedCandidateSequence Δ lam R (L₀ z)
          (sampleTimeShift Δ z (T₀ z).toNNReal) i N ≠ ⊤ := by
        intro htop
        apply hz
        rw [hRT, htop, add_top]
      obtain ⟨j, hj⟩ := roundedCandidateSequence_mem_grid Δ hΔ lam R (L₀ z) _ i N hCfin
      refine ⟨k + j, ?_⟩
      rw [hRT, hj, hk, ← ENNReal.coe_add]
      congr 1
      push_cast
      simp only [Δ]
      ring
    have hdecN := roundTime_historyDecided Δ hΔ lam R b h0 hR i T₀ hgrid₀ W₀ L₀ hdec₀ N
      (fun w : CoupledSample d => failedCoinWeight Δ lam R b i w)
    have hrest := lintegral_grid_stopping_le_of_decided_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
      TN hTN hgridN WN hWN (fun p => failedCoinWeight Δ lam R b i p.2)
      ((measurable_failedCoinWeight Δ lam R b i).comp measurable_snd) hdecN (ENNReal.ofReal ρ)
      (by
        filter_upwards [hcoin] with q hq m _
        exact hq m)
    calc ∫⁻ q, roundHistoryWeight Δ lam R b i T₀ W₀ L₀ (N + 1) q.2 ∂annealedCoupledLaw Q.measure K
        ≤ ∫⁻ q, {q : FieldPair d × CoupledSample d | TN q.2 ≠ ⊤}.indicator
            (fun q => WN q.2 * failedCoinWeight Δ lam R b i
              (sampleTimeShift Δ q.2 (TN q.2).toNNReal)) q ∂annealedCoupledLaw Q.measure K := by
          apply lintegral_mono
          intro q
          exact roundHistoryWeight_succ_le Δ hΔ lam R b i T₀ hgrid₀ W₀ L₀ N q.2
      _ ≤ ENNReal.ofReal ρ * ∫⁻ q, {q : FieldPair d × CoupledSample d | TN q.2 ≠ ⊤}.indicator
            (fun q => WN q.2) q ∂annealedCoupledLaw Q.measure K := hrest
      _ ≤ ENNReal.ofReal ρ * ∫⁻ q, WN q.2 ∂annealedCoupledLaw Q.measure K := by
          gcongr with q
          exact Set.indicator_le_self _ _ q
      _ ≤ ENNReal.ofReal ρ * (ENNReal.ofReal ρ ^ N * ENNReal.ofReal D *
            ∫⁻ q, {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2) q
              ∂annealedCoupledLaw Q.measure K) := by gcongr
      _ = _ := by ring

/-- The physical-kernel version of `EinsteinFull.Regeneration.lintegral_candidateOvershoot_le`. -/
theorem lintegral_candidateOvershoot_le_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K)
    (b D ρ : ℝ) (hb : 0 ≤ b)
    (h1st : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (m : ℕ) (L : ℝ), 0 ≤ L →
      ∫⁻ w, failedRoundWeight (Renewal.regenDelta lam) lam (l / lam) L b (Renewal.forceCoord hd) 0 w
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal D)
    (hcoin : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      ∫⁻ v, failedCoinWeight (Renewal.regenDelta lam) lam (l / lam) b (Renewal.forceCoord hd) v
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal ρ)
    (T₀ : CoupledSample d → ℝ≥0∞) (hT₀ : Measurable T₀)
    (hgrid₀ : ∀ z, T₀ z ≠ ⊤ → ∃ m : ℕ,
      T₀ z = (((m : ℝ≥0) * Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞))
    (W₀ : CoupledSample d → ℝ≥0∞) (hW₀ : Measurable W₀)
    (L₀ : CoupledSample d → ℝ) (hL₀m : Measurable L₀) (hL₀ : ∀ z, 0 ≤ L₀ z)
    (hdec₀ : HistoryDecided (Renewal.regenDelta lam) T₀ (fun z => (W₀ z, L₀ z))) :
    ∫⁻ q, {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2 *
        candidateOvershootWeight (Renewal.regenDelta lam) lam (l / lam) (L₀ q.2) b
          (Renewal.forceCoord hd) (sampleTimeShift (Renewal.regenDelta lam) q.2 (T₀ q.2).toNNReal)) q
        ∂annealedCoupledLaw Q.measure K ≤
      ENNReal.ofReal (Real.exp (b * lam * (11 * (l / lam)))) *
        ((1 - ENNReal.ofReal ρ)⁻¹ * ENNReal.ofReal D *
          ∫⁻ q, {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2) q
            ∂annealedCoupledLaw Q.measure K) := by
  let Δ := Renewal.regenDelta lam
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  let R := l / lam
  have hR : 0 < R := div_pos hl h0
  let i := Renewal.forceCoord hd
  let μ := annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure Q.measure := Q.probability
  have hshift : Measurable (fun z : CoupledSample d => sampleTimeShift Δ z (T₀ z).toNNReal) :=
    (measurable_sampleTimeShift Δ).comp (hT₀.ennreal_toNNReal.prodMk measurable_id)
  have hLHSm : Measurable (fun q : FieldPair d × CoupledSample d =>
      {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2 *
        candidateOvershootWeight Δ lam R (L₀ q.2) b i (sampleTimeShift Δ q.2 (T₀ q.2).toNNReal)) q) :=
    ((hW₀.comp measurable_snd).mul ((measurable_candidateOvershootWeight_joint Δ lam R b i).comp
      ((hL₀m.comp measurable_snd).prodMk (hshift.comp measurable_snd)))).indicator
      (measurableSet_eq_fun (hT₀.comp measurable_snd) measurable_const).compl
  have hRHSm : Measurable (fun q : FieldPair d × CoupledSample d =>
      ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
        ∑' N, roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N q.2) :=
    measurable_const.mul (measurable_tsum_ennreal fun N =>
      (measurable_roundHistoryWeight Δ lam R b i T₀ hT₀ W₀ hW₀ L₀ hL₀m N).comp measurable_snd)
  have hpoint : ∀ᵐ q ∂μ,
      {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2 *
        candidateOvershootWeight Δ lam R (L₀ q.2) b i (sampleTimeShift Δ q.2 (T₀ q.2).toNNReal)) q ≤
      ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
        ∑' N, roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N q.2 := by
    apply Measure.ae_compProd_of_ae_ae (measurableSet_le hLHSm hRHSm)
    filter_upwards [hK.1.1, hK.2.2.2.2.2.1.1] with ω hprob hsupp
    have : IsProbabilityMeasure (originCoupledLaw K ω) := hprob
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
    filter_upwards [hsupp] with z hz
    by_cases hT : T₀ z = ⊤
    · simp only [Set.indicator, Set.mem_ofPred_eq, hT, ne_eq, not_true_eq_false, ite_false]
      exact zero_le
    · obtain ⟨k, hk⟩ := hgrid₀ z hT
      have hwk : sampleTimeShift Δ z (T₀ z).toNNReal = sampleTimeShift Δ z ((k : ℝ≥0) * Δ) := by
        rw [hk, ENNReal.toNNReal_coe]
      have hsuppw := bridgeSupport_sampleTimeShift Δ hΔ i R z hz k
      rw [← hwk] at hsuppw
      have hle := candidateOvershootWeight_le Δ hΔ lam R (L₀ z) b h0 hR hb i _ hsuppw
      simp only [Set.indicator, Set.mem_ofPred_eq, hT, ne_eq, not_false_eq_true, ite_true]
      simp only [roundHistoryWeight, Set.indicator, Set.mem_ofPred_eq, hT, ne_eq,
        not_false_eq_true, ite_true]
      calc W₀ z * candidateOvershootWeight Δ lam R (L₀ z) b i (sampleTimeShift Δ z (T₀ z).toNNReal)
          ≤ W₀ z * (ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
            ∑' N, failedRoundWeight Δ lam R (L₀ z) b i N (sampleTimeShift Δ z (T₀ z).toNNReal)) := by
            gcongr
        _ = _ := by
            rw [ENNReal.tsum_mul_left, mul_left_comm]
  have hρle : ∀ N, ∫⁻ q, roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N q.2 ∂μ ≤
      ENNReal.ofReal ρ ^ N * ENNReal.ofReal D *
        ∫⁻ q, {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2) q ∂μ :=
    fun N => lintegral_roundHistoryWeight_le_phys hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK R b D ρ hR i
      h1st hcoin T₀ hT₀ hgrid₀ W₀ hW₀ L₀ hL₀m hL₀ hdec₀ N
  calc _ ≤ ∫⁻ q, ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
          ∑' N, roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N q.2 ∂μ := lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
          ∑' N, ∫⁻ q, roundHistoryWeight Δ lam R b i T₀ W₀ L₀ N q.2 ∂μ := by
        rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        congr 1
        exact lintegral_tsum fun N => ((measurable_roundHistoryWeight Δ lam R b i T₀ hT₀ W₀ hW₀ L₀
          hL₀m N).comp measurable_snd).aemeasurable
    _ ≤ ENNReal.ofReal (Real.exp (b * lam * (11 * R))) *
          ∑' N, ENNReal.ofReal ρ ^ N * (ENNReal.ofReal D *
            ∫⁻ q, {q : FieldPair d × CoupledSample d | T₀ q.2 ≠ ⊤}.indicator (fun q => W₀ q.2) q
              ∂μ) := by
        gcongr with N
        rw [← mul_assoc]
        exact hρle N
    _ = _ := by
        rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
        ring

end EinsteinFull.Regeneration
