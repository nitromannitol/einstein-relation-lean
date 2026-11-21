import EinsteinFull.PhysicalRegeneration.Vendor.Regeneration.AnnealedUniformEndpointRestart
import EinsteinFull.Regeneration.EndpointJointUniform
import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini
import EinsteinRelation.Regeneration.FiniteHistoryTrialEvent

/-!
# The annealed uniform endpoint with a factor of the endpoint displacement

For the split coupling of the physical kernel, the restart at the end of a successful interval
and the uniform law of its endpoint hold jointly with a nonnegative factor of the endpoint
displacement over the interval (GMP 2012, Proposition 5.4(ii)–(iii); Shen 2003, Theorem 2.5,
whose cycle variables contain the displacement up to the regeneration time).
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- The annealed uniform endpoint formula for a nonnegative bounded future test multiplied by a
nonnegative bounded function of the endpoint displacement over the successful interval. -/
theorem integral_annealed_future_endpoint_eq_uniformEndpointAverage_phys {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (i : Fin d) (hδ : 0 ≤ δ)
    (hR0 : volume (endpointBall i R 0) ≠ ⊤) (hRpos : volume (endpointBall i R 0) ≠ 0)
    (hRestart : HasDeterministicRestart Q.measure Δ K)
    (hUniform : HasUniformSuccessfulEndpoint Q.measure Δ δ R i K)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hbH : BoundedRealTest H) (hH0 : ∀ z, 0 ≤ H z)
    (g : Vec d → ℝ) (hg : Measurable g) (hbg : BoundedRealTest g) (hg0 : ∀ y, 0 ≤ g y)
    (Ψ : (Vec d × FieldPair d) × CoupledSample d → ℝ)
    (hΨ : Measurable Ψ) (hbΨ : BoundedRealTest Ψ)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B)
    (hB0 : ∀ p, 0 ≤ B p)
    (hBeq : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
      B xω = ∫ w, Ψ (xω, w) ∂K xω) :
    (∫ q, H q.2 * (if q.2.2 m = true then (1 : ℝ) else 0) *
      g (q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ) - q.2.1 ((m : ℝ≥0) * Δ)) *
      Ψ ((q.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), q.1),
        sampleTimeShift Δ q.2 (((m + 1 : ℕ) : ℝ≥0) * Δ))
      ∂annealedCoupledLaw Q.measure K) =
      ∫ ω, δ * ∫ z, H z * endpointAverage i R (z.1 ((m : ℝ≥0) * Δ))
        (fun y => g (y - z.1 ((m : ℝ≥0) * Δ)) * B (y, ω)) ∂K (0, ω) ∂Q.measure := by
  classical
  let t : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0) * Δ
  let s : ℝ≥0 := (m : ℝ≥0) * Δ
  have ht : 0 < t := mul_pos (by positivity) hΔ
  have hprob := ae_quenched_of_annealed Q.measure K hK
    (ae_at_endpoint_of_product_ae_phys hd Q lam h0 h1 P K hK hpath hP t ht _ hK.2)
  have hversion := ae_quenched_of_annealed Q.measure K hK
    (ae_at_endpoint_of_product_ae_phys hd Q lam h0 h1 P K hK hpath hP t ht _ hBeq)
  let F : FieldPair d × CoupledSample d → ℝ := fun q =>
    H q.2 * (if q.2.2 m = true then 1 else 0) * g (q.2.1 t - q.2.1 s) *
      Ψ ((q.2.1 t, q.1), sampleTimeShift Δ q.2 t)
  have hHfull := hH.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hte : Measurable fun q : FieldPair d × CoupledSample d => q.2.1 t :=
    (continuous_eval_const t).measurable.comp measurable_snd.fst
  have hse : Measurable fun q : FieldPair d × CoupledSample d => q.2.1 s :=
    (continuous_eval_const s).measurable.comp measurable_snd.fst
  have hF : Measurable F := by
    exact (((hHfull.comp measurable_snd).mul
      (Measurable.ite (measurableSet_eq_fun ((measurable_pi_apply m).comp measurable_snd.snd)
        measurable_const) measurable_const measurable_const)).mul (hg.comp (hte.sub hse))).mul
      (hΨ.comp ((hte.prodMk measurable_fst).prodMk ((measurable_sampleTimeShift Δ).comp
          (measurable_const.prodMk measurable_snd))))
  obtain ⟨CH, hCH⟩ := hbH
  obtain ⟨Cg, hCg⟩ := hbg
  obtain ⟨CP, hCP⟩ := hbΨ
  have hbF : BoundedRealTest F := by
    refine ⟨max CH 0 * max Cg 0 * max CP 0, fun q => ?_⟩
    dsimp only [F]
    have hc : |(if q.2.2 m = true then (1 : ℝ) else 0)| ≤ 1 := by split_ifs <;> norm_num
    rw [abs_mul, abs_mul, abs_mul]
    calc |H q.2| * |(if q.2.2 m = true then (1 : ℝ) else 0)| * |g (q.2.1 t - q.2.1 s)| *
          |Ψ ((q.2.1 t, q.1), sampleTimeShift Δ q.2 t)| ≤
          max CH 0 * 1 * max Cg 0 * max CP 0 := by
          gcongr
          · exact (hCH _).trans (le_max_left _ _)
          · exact (hCg _).trans (le_max_left _ _)
          · exact (hCP _).trans (le_max_left _ _)
      _ = max CH 0 * max Cg 0 * max CP 0 := by ring
  change (∫ q, F q ∂annealedCoupledLaw Q.measure K) = _
  rw [integral_annealedCoupledLaw Q.measure K hK F hF hbF]
  apply integral_congr_ae
  filter_upwards [hK.1, hRestart.1, hUniform.1, hprob, hversion] with ω hω hr hu hp hv
  have : IsProbabilityMeasure (K (0, ω)) := hω
  exact integral_future_endpoint_eq_uniformEndpointAverage Δ δ R i K (0, ω) hr hu hδ hR0 hRpos
    m hp H hH ⟨CH, hCH⟩ hH0 g hg ⟨Cg, hCg⟩ hg0 (fun q => Ψ ((q.1, ω), q.2))
    (hΨ.comp ((measurable_fst.prodMk measurable_const).prodMk measurable_snd))
    ⟨CP, fun q => hCP _⟩ (fun y => B (y, ω)) (hB.comp measurable_prodMk_right)
    (by obtain ⟨C, hC⟩ := hbB; exact ⟨C, fun y => hC _⟩) (fun y => hB0 _) hv

open Classical in
/-- Annealed endpoint averaging with a factor of the endpoint displacement gives the spatial
integral of the weighted past kernel against a bounded future version. -/
theorem integral_annealed_endpointAverage_fubini_endpoint {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (m : ℕ) (i : Fin d) (R : ℝ) (hR : 0 < R)
    (G : CoupledSample d → ℝ) (hG : Measurable G) (hbG : BoundedRealTest G)
    (g : Vec d → ℝ) (hg : Measurable g) (hbg : BoundedRealTest g)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B) :
    (∫ ω, ∫ z, G z * endpointAverage i R (z.1 ((m : ℝ≥0) * Δ))
        (fun y => g (y - z.1 ((m : ℝ≥0) * Δ)) * B (y, ω)) ∂K (0, ω) ∂Q) =
      (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ *
        ∫ y, ∫ ω, (∫ z, G z * g (y - z.1 ((m : ℝ≥0) * Δ)) *
          (if y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) then 1 else 0) ∂K (0, ω)) *
          B (y, ω) ∂Q := by
  classical
  let μ := annealedCoupledLaw Q K
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q K hK
  let X : FieldPair d × CoupledSample d → Vec d := fun q => q.2.1 ((m : ℝ≥0) * Δ)
  let B' : (FieldPair d × CoupledSample d) × Vec d → ℝ := fun q =>
    g (q.2 - X q.1) * B (q.2, q.1.1)
  have hX : Measurable X := (continuous_eval_const _).measurable.comp measurable_snd.fst
  have hB' : Measurable B' :=
    (hg.comp (measurable_snd.sub (hX.comp measurable_fst))).mul
      (hB.comp (measurable_snd.prodMk measurable_fst.fst))
  obtain ⟨Cg, hCg⟩ := hbg
  obtain ⟨CB, hCB⟩ := hbB
  have hbB' : BoundedRealTest B' := ⟨max Cg 0 * max CB 0, fun q => by
    rw [abs_mul]
    exact mul_le_mul ((hCg _).trans (le_max_left _ _)) ((hCB _).trans (le_max_left _ _))
      (abs_nonneg _) (le_max_right _ _)⟩
  let F : FieldPair d × CoupledSample d → ℝ := fun q =>
    G q.2 * endpointAverage i R (X q) (fun y => B' (q, y))
  have hF : Measurable F := (hG.comp measurable_snd).mul
    (measurable_endpointAverage i R X hX B' hB')
  have hbF : BoundedRealTest F := by
    obtain ⟨CG, hCG⟩ := hbG
    obtain ⟨CA, hCA⟩ := boundedRealTest_endpointAverage i R hR X B' hbB'
    refine ⟨max CG 0 * max CA 0, fun q => ?_⟩
    dsimp [F]
    rw [abs_mul]
    exact mul_le_mul ((hCG _).trans (le_max_left _ _))
      ((hCA _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
  have hdis := integral_annealedCoupledLaw Q K hK F hF hbF
  change (∫ ω, ∫ z, F (ω, z) ∂K (0, ω) ∂Q) = _
  rw [← hdis]
  have hfu := integral_mul_endpointAverage_eq μ i R hR X hX
    (fun q => G q.2) (hG.comp measurable_snd)
    (by obtain ⟨C, hC⟩ := hbG; exact ⟨C, fun q => hC _⟩) B' hB' hbB'
  refine hfu.trans (congrArg (fun a => (volume (endpointBall i R (0 : Vec d))).toReal⁻¹ * a)
    (integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)))
  let J : FieldPair d × CoupledSample d → ℝ := fun q =>
    (endpointBall i R (X q)).indicator (fun y => G q.2 * B' (q, y)) y
  have hset : MeasurableSet {q : FieldPair d × CoupledSample d |
      y ∈ endpointBall i R (X q)} :=
    (measurableSet_endpointBall_pair i R).preimage (hX.prodMk measurable_const)
  have hJ : Measurable J :=
    ((hG.comp measurable_snd).mul (hB'.comp (measurable_id.prodMk measurable_const))).indicator
      hset
  have hbJ : BoundedRealTest J := by
    obtain ⟨CG, hCG⟩ := hbG
    obtain ⟨CC, hCC⟩ := hbB'
    refine ⟨max CG 0 * max CC 0, fun q => ?_⟩
    by_cases hq : y ∈ endpointBall i R (X q)
    · simp only [J, Set.indicator_of_mem hq, abs_mul]
      exact mul_le_mul ((hCG _).trans (le_max_left _ _))
        ((hCC _).trans (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    · simpa only [J, Set.indicator_of_notMem hq, abs_zero] using
        (mul_nonneg (le_max_right CG (0 : ℝ)) (le_max_right CC (0 : ℝ)))
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
  by_cases hz : y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ))
  · simp only [J, X, B', Set.indicator_of_mem hz, hz, ↓reduceIte]
    ring
  · simp only [J, X, Set.indicator_of_notMem hz, hz, ↓reduceIte]
    ring

open Classical in
/-- The spatial integral on a first regeneration slice with a factor of the last bridge
displacement, for the split coupling of the physical kernel and nonnegative bounded tests: the
displacement enters the past kernel through the endpoint, and the future enters through its
kernel version at the endpoint. -/
theorem firstRegeneration_slice_integral_endpoint_eq_phys {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : IsGMPPhysicalKernelReducedBound hd Q.ellipticity_parameter Q lam h0 h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d) (hδ : 0 ≤ δ)
    (hR0 : volume (endpointBall i R 0) ≠ ⊤) (hRpos : volume (endpointBall i R 0) ≠ 0)
    (hRestart : HasDeterministicRestart Q.measure Δ K)
    (hUniform : HasUniformSuccessfulEndpoint Q.measure Δ δ R i K)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hb : BoundedRealTest Φ)
    (hΦ0 : ∀ r, 0 ≤ Φ r)
    (B : Vec d × FieldPair d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B)
    (hB0 : ∀ p, 0 ≤ B p)
    (hBp : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
      B xω = ∫ z, killedFutureTest R i Φ (xω, z) ∂K xω)
    (m : ℕ) (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hbH : BoundedRealTest H) (hH0 : ∀ z, 0 ≤ H z)
    (g : Vec d → ℝ) (hg : Measurable g) (hbg : BoundedRealTest g) (hg0 : ∀ y, 0 ≤ g y) :
    (∫ p in {p : FieldPair d × CoupledSample d | firstRegenerationTime Δ lam R p.2 i =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
      H p.2 * g (p.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ) - p.2.1 ((m : ℝ≥0) * Δ)) *
        Φ (iteratedRecord Δ lam R i 1 p) ∂annealedCoupledLaw Q.measure K) =
      (δ / (volume (endpointBall i R (0 : Vec d))).toReal) *
        ∫ y, ∫ ω, (∫ z, ((forcedBitTrialEvent Δ lam R i m).indicator H) z *
          g (y - z.1 ((m : ℝ≥0) * Δ)) *
          (if y ∈ endpointBall i R (z.1 ((m : ℝ≥0) * Δ)) then 1 else 0) ∂K (0, ω)) *
          B (y, ω) ∂Q.measure := by
  let G := (forcedBitTrialEvent Δ lam R i m).indicator H
  have hG : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance G :=
    hH.indicator (measurableSet_forcedBitTrialEvent_finiteHistory Δ hΔ lam R hR i m)
  have hG0 : ∀ z, 0 ≤ G z := fun z => by
    by_cases hz : z ∈ forcedBitTrialEvent Δ lam R i m
    · simp only [G, Set.indicator_of_mem hz]; exact hH0 z
    · simp only [G, Set.indicator_of_notMem hz, le_refl]
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
  have hΨ0 : ∀ q, 0 ≤ killedFutureTest R i Φ q := fun q => by
    unfold killedFutureTest
    split_ifs
    · exact hΦ0 _
    · exact le_refl 0
  rw [← integral_indicator hsm]
  have hpt : ∀ p : FieldPair d × CoupledSample d,
      {p : FieldPair d × CoupledSample d | firstRegenerationTime Δ lam R p.2 i =
          ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}.indicator
        (fun p => H p.2 * g (p.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ) - p.2.1 ((m : ℝ≥0) * Δ)) *
          Φ (iteratedRecord Δ lam R i 1 p)) p =
      G p.2 * (if p.2.2 m = true then (1 : ℝ) else 0) *
        g (p.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ) - p.2.1 ((m : ℝ≥0) * Δ)) *
        killedFutureTest R i Φ ((p.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), p.1),
          sampleTimeShift Δ p.2 (((m + 1 : ℕ) : ℝ≥0) * Δ)) := by
    intro p
    have h := firstRegeneration_slice_integrand Δ hΔ lam R i m H Φ p
    have e : (fun p : FieldPair d × CoupledSample d =>
        H p.2 * g (p.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ) - p.2.1 ((m : ℝ≥0) * Δ)) *
          Φ (iteratedRecord Δ lam R i 1 p)) =
        fun p => g (p.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ) - p.2.1 ((m : ℝ≥0) * Δ)) *
          (H p.2 * Φ (iteratedRecord Δ lam R i 1 p)) := by
      funext p
      ring
    rw [e, Set.indicator_mul_right, h]
    ring
  simp_rw [hpt]
  rw [integral_annealed_future_endpoint_eq_uniformEndpointAverage_phys hd Q lam h0 h1 P K hK
    hpath hP Δ hΔ δ R i hδ hR0 hRpos hRestart hUniform m G hG hbG hG0 g hg hbg hg0
    (killedFutureTest R i Φ) (measurable_killedFutureTest R i Φ hΦ)
    (boundedRealTest_killedFutureTest R i Φ hb) B hB hbB hB0 hBp, integral_const_mul,
    integral_annealed_endpointAverage_fubini_endpoint Q.measure K hK Δ m i R hR G
      (hG.mono (Probability.finiteHistorySigma_le Δ m) le_rfl) hbG g hg hbg B hB hbB]
  simp only [G, div_eq_mul_inv, mul_assoc]

end EinsteinFull.Regeneration
