import EinsteinRelation.Regeneration.FirstRegenerationEndpointFormula
import EinsteinRelation.Regeneration.EndpointAverageFubini

/-!
# The spatial Fubini formula on regeneration slices

Source `paper/main.tex:383–397`, `regen.slice-factor`. The past integral is
the literal quenched expectation of the forced trial event, the past test
and the endpoint-ball indicator. Restart, the successful endpoint law and
Fubini give the spatial integral of its product with the killed future.
No locality or independence is assumed in this calculation.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

/-- The quenched past factor `A_n(y,ω)` of `paper/main.tex:385–388`, with
`n = m + 1` and the literal forced-bit trial event. -/
def firstSlicePastIntegral {d : ℕ} (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (m : ℕ)
    (K : CoupledQuenchedLaws d) (H : CoupledSample d → ℝ)
    (yω : Vec d × FieldPair d) : ℝ :=
  ∫ z, ((forcedBitTrialEvent Δ lam R i m).indicator H) z *
    (if yω.1 ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) then 1 else 0) ∂K (0, yω.2)

/-- Annealed endpoint averaging gives the spatial integral of the past
kernel and a bounded future version (`paper/main.tex:391–397`). -/
theorem integral_annealed_endpointAverage_fubini {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (m : ℕ) (i : Fin d) (R : ℝ) (hR : 0 < R)
    (G : CoupledSample d → ℝ) (hG : Measurable G) (hbG : BoundedRealTest G)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B) :
    (∫ ω, ∫ z, G z * endpointAverage i R (z.1 ((m : ℝ≥0) * Δ))
        (fun y => B (y, ω)) ∂K (0, ω) ∂Q) =
      (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
        ∫ y, ∫ ω, (∫ z, G z *
          (if y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) then 1 else 0) ∂K (0, ω)) *
          B (y, ω) ∂Q := by
  classical
  let μ := annealedCoupledLaw Q K
  haveI : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  let X : FieldPair d × CoupledSample d → Vec d := fun q => q.2.1 ((m : ℝ≥0) * Δ)
  let B' : (FieldPair d × CoupledSample d) × Vec d → ℝ := fun q => B (q.2, q.1.1)
  have hX : Measurable X := (continuous_eval_const _).measurable.comp measurable_snd.fst
  have hB' : Measurable B' := hB.comp (measurable_snd.prodMk measurable_fst.fst)
  have hbB' : BoundedRealTest B' := by
    obtain ⟨C, hC⟩ := hbB
    exact ⟨C, fun q => hC _⟩
  let F : FieldPair d × CoupledSample d → ℝ := fun q =>
    G q.2 * endpointAverage i R (X q) (fun y => B' (q, y))
  have hF : Measurable F := (hG.comp measurable_snd).mul
    (measurable_endpointAverage i R X hX B' hB')
  have hbF : BoundedRealTest F := by
    obtain ⟨CG, hCG⟩ := hbG
    obtain ⟨CB, hCB⟩ := boundedRealTest_endpointAverage i R hR X B' hbB'
    refine ⟨max CG 0 * max CB 0, fun q => ?_⟩
    dsimp [F]
    rw [abs_mul]
    exact mul_le_mul ((hCG _).trans (le_max_left _ _))
      ((hCB _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  have hdis := integral_annealedCoupledLaw Q K hK F hF hbF
  change (∫ ω, ∫ z, F (ω, z) ∂K (0, ω) ∂Q) = _
  rw [← hdis]
  have hfu := integral_mul_endpointAverage_eq μ i R hR X hX
    (fun q => G q.2) (hG.comp measurable_snd)
    (by obtain ⟨C, hC⟩ := hbG; exact ⟨C, fun q => hC _⟩) B' hB' hbB'
  refine hfu.trans (congrArg (fun a => (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ * a)
    (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)))
  let J : FieldPair d × CoupledSample d → ℝ := fun q =>
    (endpointBall i R (X q)).indicator (fun y => G q.2 * B (y, q.1)) y
  have hset : MeasurableSet {q : FieldPair d × CoupledSample d |
      y ∈ endpointBall i R (X q)} :=
    (measurableSet_endpointBall_pair i R).preimage (hX.prodMk measurable_const)
  have hJ : Measurable J :=
    ((hG.comp measurable_snd).mul (hB.comp (measurable_const.prodMk measurable_fst))).indicator hset
  have hbJ : BoundedRealTest J := by
    obtain ⟨CG, hCG⟩ := hbG
    obtain ⟨CB, hCB⟩ := hbB
    refine ⟨max CG 0 * max CB 0, fun q => ?_⟩
    by_cases hq : y ∈ endpointBall i R (X q)
    · simp only [J, Set.indicator_of_mem hq, abs_mul]
      exact mul_le_mul ((hCG _).trans (le_max_left _ _))
        ((hCB _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    · simpa only [J, Set.indicator_of_notMem hq, abs_zero] using
        (mul_nonneg (le_max_right CG (0 : ℝ)) (le_max_right CB (0 : ℝ)))
  have hdisJ := integral_annealedCoupledLaw Q K hK J hJ hbJ
  change (∫ q, J q ∂μ) = _
  rw [hdisJ]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  dsimp only
  rw [← integral_mul_const]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro z
  by_cases hz : y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) <;> simp [J, X, hz]

/-- The full spatial integral in `regen.slice-factor`, before the
finite-range step, holds for the literal regeneration time and every
bounded measurable future-record test. -/
theorem firstRegeneration_slice_integral_eq {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
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
  rw [integral_annealed_future_eq_uniformEndpointAverage hd Q lam h0 h1 P K hK hpath hP
    Δ hΔ δ R i hRestart hUniform m G hG hbG (killedFutureTest R i Φ)
    (measurable_killedFutureTest R i Φ hΦ) (boundedRealTest_killedFutureTest R i Φ hb)
    B hB hbB hBp, integral_const_mul,
    integral_annealed_endpointAverage_fubini Q.measure K hK Δ m i R hR G
      (hG.mono (Probability.finiteHistorySigma_le Δ m) le_rfl) hbG B hB hbB]
  simp only [firstSlicePastIntegral, G, div_eq_mul_inv, mul_assoc]


end EinsteinRelation.Regeneration
