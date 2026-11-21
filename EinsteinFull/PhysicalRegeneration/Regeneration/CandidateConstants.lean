import EinsteinFull.Regeneration.CandidateConstants
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
import EinsteinFull.PhysicalRegeneration.Regeneration.CoupledCandidateMoment
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
`EinsteinFull.Regeneration.CandidateConstants`

The declarations of that module that concern the reduced quenched kernel, stated and
proved for the physical quenched kernel of GMP Section 7: the zero-potential pair
`(exp(-2V) a₀, 0)` is replaced by the physical pair `ω = (a₀, V)`, regular at the same
bound `sourceReducedBound Λ₀` (`IsGMPPhysicalKernelReducedBound`).
-/


open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal
namespace EinsteinFull.Regeneration
attribute [local irreducible] firstRoundedCandidate roundedCandidateSequence passageSequence
  firstSuccessfulCandidate
/-- The physical-kernel version of `EinsteinFull.Regeneration.uniform_candidate_round_constants`. -/
theorem uniform_candidate_round_constants_phys {d : ℕ} (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ) (hl : 0 < l)
    (δ : ℝ) (hδ0 : 0 < δ) (hδ1 : δ < 1) :
    ∃ a₂ D₁ ρ : ℝ, 0 < a₂ ∧ 0 ≤ D₁ ∧ 0 ≤ ρ ∧ ρ < 1 ∧
      ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1)
        (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d),
        IsRegenerationCouplingPhys hd Q lam l δ h0.le h1 P K →
        (∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (m : ℕ) (L : ℝ), 0 ≤ L →
          ∫⁻ w, failedRoundWeight (Renewal.regenDelta lam) lam (l / lam) L a₂
            (Renewal.forceCoord hd) 0 w
            ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal D₁) ∧
        (∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ m : ℕ,
          ∫⁻ v, failedCoinWeight (Renewal.regenDelta lam) lam (l / lam) a₂
            (Renewal.forceCoord hd) v
            ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal ρ) := by
  obtain ⟨b, D, hb, hD, hcand⟩ := uniform_first_candidate_height_phys hd Λ₀ r₀ l hl
  let c₁ : ℝ := Real.log (1 + δ / 4) / (6 * l)
  have hc₁ : 0 < c₁ := div_pos (Real.log_pos (by linarith)) (by positivity)
  let a₂ : ℝ := min (b / 2) (min c₁ (δ * b / (16 * (D + 1))))
  have ha₂ : 0 < a₂ := lt_min (by positivity) (lt_min hc₁ (by positivity))
  have ha₂b : 2 * a₂ ≤ b := by
    have := min_le_left (b / 2) (min c₁ (δ * b / (16 * (D + 1))))
    linarith
  have ha₂c : a₂ ≤ c₁ := (min_le_right _ _).trans (min_le_left _ _)
  have ha₂d : a₂ ≤ δ * b / (16 * (D + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  let E₂ : ℝ := Real.exp (6 * a₂ * l) * (1 + 2 * a₂ / b * D)
  have hexp : Real.exp (6 * a₂ * l) ≤ 1 + δ / 4 := by
    have h : 6 * a₂ * l ≤ Real.log (1 + δ / 4) := by
      have := mul_le_mul_of_nonneg_right ha₂c (by positivity : (0 : ℝ) ≤ 6 * l)
      simp only [c₁] at this
      rw [div_mul_cancel₀ _ (by positivity : (6 * l : ℝ) ≠ 0)] at this
      linarith
    calc Real.exp (6 * a₂ * l) ≤ Real.exp (Real.log (1 + δ / 4)) := Real.exp_le_exp.mpr h
      _ = 1 + δ / 4 := Real.exp_log (by linarith)
  have hlin : 2 * a₂ / b * D ≤ δ / 8 := by
    have h1 : 2 * a₂ / b ≤ δ / (8 * (D + 1)) := by
      rw [div_le_iff₀ hb]
      have := mul_le_mul_of_nonneg_left ha₂d (by norm_num : (0 : ℝ) ≤ 2)
      calc 2 * a₂ ≤ 2 * (δ * b / (16 * (D + 1))) := this
        _ = δ / (8 * (D + 1)) * b := by field_simp; ring
    calc 2 * a₂ / b * D ≤ δ / (8 * (D + 1)) * D := mul_le_mul_of_nonneg_right h1 hD.le
      _ ≤ δ / 8 := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith
  have hE₂ : E₂ ≤ 1 + δ / 2 := by
    have h0' : 0 ≤ 2 * a₂ / b * D := by positivity
    calc E₂ ≤ (1 + δ / 4) * (1 + δ / 8) :=
          mul_le_mul hexp (by linarith) (by linarith) (by linarith)
      _ ≤ 1 + δ / 2 := by nlinarith
  refine ⟨a₂, 1 + a₂ / b * D, (1 / 2) * ((1 - δ) + E₂), ha₂, by positivity, ?_, ?_, ?_⟩
  · have : 0 ≤ E₂ := by positivity
    have : 0 ≤ 1 - δ := by linarith
    positivity
  · linarith
  intro Q lam h0 h1 P K hK
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hlR : lam * R = l := by simp only [R]; field_simp
  have hgood := hcand Q lam h0 h1 P hK.2.2.1
  have hprob : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, IsProbabilityMeasure (P (x, ω)) := by
    filter_upwards [hK.2.2.1] with ω hω x
    obtain ⟨_, G, hrow⟩ := hω
    rw [hrow x]
    exact G.pathLaw_isMarkovKernel.isProbabilityMeasure x
  constructor
  · apply inner_first_round_le_phys hd Q lam h0 h1 l δ P K hK R a₂ (1 + a₂ / b * D) i
    filter_upwards [hgood, hprob] with ω hω hp x L hL
    have hp' := hp x
    calc ∫⁻ γ, firstCandidateWeight Δ lam R L a₂ i γ ∂P (x, ω)
        ≤ ∫⁻ γ, 1 + ENNReal.ofReal (a₂ / b) * firstCandidateWeight Δ lam R L b i γ ∂P (x, ω) :=
          lintegral_mono fun γ => firstCandidateWeight_le_tilt Δ lam R L a₂ b ha₂.le
            (by linarith) hb i γ
      _ = 1 + ENNReal.ofReal (a₂ / b) * ∫⁻ γ, firstCandidateWeight Δ lam R L b i γ ∂P (x, ω) := by
          rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, one_mul,
            lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ 1 + ENNReal.ofReal (a₂ / b) * ENNReal.ofReal D := by
          gcongr
          exact hω x i L hL
      _ = ENNReal.ofReal (1 + a₂ / b * D) := by
          rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
            ← ENNReal.ofReal_add zero_le_one (by positivity)]
  · have hE : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
        ∫⁻ γ, squaredRestartWeight Δ lam R a₂ i γ ∂P (x, ω) ≤ ENNReal.ofReal E₂ := by
      filter_upwards [hgood, hprob] with ω hω hp x
      have hp' := hp x
      have h3 : 0 ≤ 3 * lam * R := by positivity
      calc ∫⁻ γ, squaredRestartWeight Δ lam R a₂ i γ ∂P (x, ω)
          ≤ ∫⁻ γ, ENNReal.ofReal (Real.exp (6 * a₂ * (lam * R))) *
              (1 + ENNReal.ofReal (2 * a₂ / b) *
                firstCandidateWeight Δ lam R (3 * lam * R) b i γ) ∂P (x, ω) :=
            lintegral_mono fun γ => squaredRestartWeight_le_tilt Δ lam R a₂ b h0 ha₂.le ha₂b hb i γ
        _ = ENNReal.ofReal (Real.exp (6 * a₂ * (lam * R))) *
              (1 + ENNReal.ofReal (2 * a₂ / b) *
                ∫⁻ γ, firstCandidateWeight Δ lam R (3 * lam * R) b i γ ∂P (x, ω)) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, lintegral_add_left measurable_const,
              lintegral_const, measure_univ, one_mul,
              lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
        _ ≤ ENNReal.ofReal (Real.exp (6 * a₂ * (lam * R))) *
              (1 + ENNReal.ofReal (2 * a₂ / b) * ENNReal.ofReal D) := by
            gcongr
            exact hω x i (3 * lam * R) h3
        _ = ENNReal.ofReal E₂ := by
            rw [← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_one,
              ← ENNReal.ofReal_add zero_le_one (by positivity),
              ← ENNReal.ofReal_mul (Real.exp_pos _).le, hlR]
    have hc := inner_failed_coin_le_phys hd Q lam h0 h1 l δ P K hK R a₂ E₂ i hE
    filter_upwards [hc] with q hq m
    refine (hq m).trans (le_of_eq ?_)
    rw [← ENNReal.ofReal_add (by linarith) (by positivity), ← ENNReal.ofReal_mul (by norm_num)]

end EinsteinFull.Regeneration
