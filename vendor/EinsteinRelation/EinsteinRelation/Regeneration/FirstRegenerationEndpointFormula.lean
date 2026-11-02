import EinsteinRelation.Regeneration.AnnealedUniformEndpointRestart
import EinsteinRelation.Regeneration.BoundedMeasurableKilledFutureVersion
import EinsteinRelation.Regeneration.FiniteHistoryTrialEvent
import EinsteinRelation.Regeneration.RenewalRecordIteration

/-!
# The actual regeneration slice as a uniform endpoint integral

Source `paper/main.tex:383–397`, the restart and uniform-endpoint calculation
in `regen.slice-factor`. The formula is established for the literal trial
construction and every bounded measurable restricted-future test. Half-space
locality and finite-range factorization are separate internal obligations.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinRelation.Regeneration

/-- The restricted future at a physical starting point, before time shifting
(`paper/main.tex:387–390`). -/
def spatialFutureRecord {d : ℕ} (R : ℝ) (i : Fin d)
    (xω : Vec d × FieldPair d) (z : CoupledSample d) : FutureState d i R :=
  ((recenterSample xω.1 z).1, z.2,
    fun x => ((translate xω.1 (reduce xω.2)).1 x, (translate xω.1 (reduce xω.2)).2 x))

/-- The future test killed on backtracking (`paper/main.tex:387–390`). -/
def killedFutureTest {d : ℕ} (R : ℝ) (i : Fin d) (Φ : FutureState d i R → ℝ)
    (q : (Vec d × FieldPair d) × CoupledSample d) : ℝ :=
  if NoBacktracking R q.2.1 i then Φ (spatialFutureRecord R i q.1 q.2) else 0

theorem measurable_killedFutureTest {d : ℕ} (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) :
    Measurable (killedFutureTest R i Φ) := by
  classical
  exact Measurable.ite ((measurableSet_NoBacktracking R i).preimage measurable_snd.fst)
    (hΦ.comp (measurable_spatial_future_triple R i)) measurable_const

theorem boundedRealTest_killedFutureTest {d : ℕ} (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (hb : BoundedRealTest Φ) :
    BoundedRealTest (killedFutureTest R i Φ) := by
  classical
  obtain ⟨C, hC⟩ := hb
  refine ⟨max C 0, fun q => ?_⟩
  dsimp [killedFutureTest]
  split_ifs
  · exact (hC _).trans (le_max_left _ _)
  · simpa only [abs_zero] using (le_max_right C 0)

/-- Time shift followed by spatial recentering is precisely the record in
the source, with the same shifted Bernoulli sequence. -/
theorem spatialFutureRecord_sampleTimeShift {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (ω : FieldPair d) (z : CoupledSample d) (t : ℝ≥0) :
    spatialFutureRecord R i (z.1 t, ω) (sampleTimeShift Δ z t) =
      futureRecord Δ R ω z i t := rfl

theorem killedFutureTest_sampleTimeShift {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (ω : FieldPair d) (z : CoupledSample d) (t : ℝ≥0) :
    killedFutureTest R i Φ ((z.1 t, ω), sampleTimeShift Δ z t) =
      if NoBacktracking R (pathTimeShift z.1 t) i then Φ (futureRecord Δ R ω z i t)
      else 0 := rfl

/-- The literal slice integrand equals the forced-past, last-bit and killed
future product (`paper/main.tex:383–397`). -/
theorem firstRegeneration_slice_integrand {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (lam R : ℝ) (i : Fin d) (m : ℕ) (H : CoupledSample d → ℝ)
    (Φ : FutureState d i R → ℝ) (p : FieldPair d × CoupledSample d) :
    ({q : FieldPair d × CoupledSample d | firstRegenerationTime Δ lam R q.2 i =
        ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}.indicator
      (fun q => H q.2 * Φ (iteratedRecord Δ lam R i 1 q))) p =
    ((forcedBitTrialEvent Δ lam R i m).indicator H) p.2 *
      (if p.2.2 m = true then (1 : ℝ) else 0) *
      killedFutureTest R i Φ ((p.2.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), p.1),
        sampleTimeShift Δ p.2 (((m + 1 : ℕ) : ℝ≥0) * Δ)) := by
  classical
  let t : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0) * Δ
  have hs := firstRegenerationTime_eq_iff_forcedBitTrialEvent Δ hΔ lam R p.2 i m
  have hrecord : firstRegenerationTime Δ lam R p.2 i = (t : ℝ≥0∞) →
      iteratedRecord Δ lam R i 1 p = futureRecord Δ R p.1 p.2 i t := by
    intro ht
    simp only [iteratedRecord, regenerationTime_one, ht, ENNReal.toNNReal_coe]
  by_cases ht : firstRegenerationTime Δ lam R p.2 i = (t : ℝ≥0∞)
  · obtain ⟨hG, hb, hD⟩ := hs.mp ht
    simp only [Set.indicator_of_mem (show p ∈ {q | firstRegenerationTime Δ lam R q.2 i =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} from ht), hrecord ht,
      Set.indicator_of_mem hG, hb, ↓reduceIte, mul_one]
    rw [killedFutureTest_sampleTimeShift, if_pos hD]
  · have hnot : ¬(p.2 ∈ forcedBitTrialEvent Δ lam R i m ∧ p.2.2 m = true ∧
        NoBacktracking R (pathTimeShift p.2.1 t) i) := fun h => ht (hs.mpr h)
    rw [Set.indicator_of_notMem (show p ∉ {q | firstRegenerationTime Δ lam R q.2 i =
      ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)} from ht)]
    by_cases hG : p.2 ∈ forcedBitTrialEvent Δ lam R i m
    · rw [Set.indicator_of_mem hG]
      by_cases hb : p.2.2 m = true
      · have hD : ¬NoBacktracking R (pathTimeShift p.2.1 t) i :=
          fun h => hnot ⟨hG, hb, h⟩
        dsimp only [t] at hD
        rw [killedFutureTest_sampleTimeShift, if_neg hD, mul_zero]
      · simp [hb]
    · rw [Set.indicator_of_notMem hG, zero_mul, zero_mul]

/-- A single bounded jointly measurable killed-future version gives the
actual uniform-endpoint formula on every positive regeneration slice.
No half-space locality or renewal identity is assumed here. -/
theorem exists_killed_future_version_slice_integral {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hpath : HasPathMarginals Q.measure K P)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (hRestart : HasDeterministicRestart Q.measure Δ K)
    (hUniform : HasUniformSuccessfulEndpoint Q.measure Δ δ R i K)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hb : BoundedRealTest Φ) :
    ∃ B : Vec d × FieldPair d → ℝ, Measurable B ∧ BoundedRealTest B ∧
      (∀ᵐ ω ∂Q.measure, B (0, ω) = ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω)) ∧
      (∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q.measure,
        B xω = ∫ z, killedFutureTest R i Φ (xω, z) ∂K xω) ∧
      ∀ (m : ℕ) (H : CoupledSample d → ℝ),
        @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H →
        BoundedRealTest H →
        (∫ p in {p : FieldPair d × CoupledSample d | firstRegenerationTime Δ lam R p.2 i =
            ((((m + 1 : ℕ) : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          H p.2 * Φ (iteratedRecord Δ lam R i 1 p) ∂annealedCoupledLaw Q.measure K) =
          ∫ ω, δ * ∫ z, ((forcedBitTrialEvent Δ lam R i m).indicator H) z *
            endpointAverage i R (z.1 ((m : ℝ≥0) * Δ)) (fun y => B (y, ω))
            ∂K (0, ω) ∂Q.measure := by
  classical
  obtain ⟨C, _, B, hB, hbB, hBo, hBp⟩ :=
    exists_globally_bounded_measurable_killed_future_version Q.measure K hK R i Φ hΦ hb
  refine ⟨B, hB, ⟨C, hbB⟩, hBo, hBp, ?_⟩
  intro m H hH hbH
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
  exact integral_annealed_future_eq_uniformEndpointAverage hd Q lam h0 h1 P K hK hpath hP
    Δ hΔ δ R i hRestart hUniform m G hG hbG (killedFutureTest R i Φ)
    (measurable_killedFutureTest R i Φ hΦ) (boundedRealTest_killedFutureTest R i Φ hb)
    B hB ⟨C, hbB⟩ hBp


end EinsteinRelation.Regeneration
