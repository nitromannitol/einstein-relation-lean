import EinsteinFull.Calculus.C10FutureKernelMonotoneClass
import EinsteinFull.Calculus.C9FutureKernelIndicatorLocality
import EinsteinFull.Work.W1.StoppedKernelLocalitySupport
import Mathlib.Probability.Kernel.Composition.Prod

/-!
# The actual killed future-record measure

The measure below retains the path, every coin and both restricted reduced
fields. Probability-part totalization changes no origin probability fibre.
These identities do not assert locality of the supplied weak-GMP coupling.
-/

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.Regeneration EinsteinRelation.Diffusion

/-- Push the surviving part of the actual origin law to the full future record.
Exceptional nonprobability fibres are totalized by zero. -/
def sbxS2KilledFutureRecordLaw {d : ℕ} (R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d) (ω : FieldPair d) : Measure (FutureState d i R) :=
  ((Probability.probabilityPart (originCoupledLaw K) ω).restrict
    {z | NoBacktracking R z.1 i}).map (spatialFutureRecord R i (0, ω))

theorem sbxS2_measurable_originFutureRecord {d : ℕ} (R : ℝ) (i : Fin d)
    (ω : FieldPair d) : Measurable (spatialFutureRecord R i (0, ω)) :=
  (measurable_spatial_future_triple R i).comp
    (measurable_const.prodMk measurable_id)

/-- The killed-record measures are subprobabilities on every fibre, including
exceptional fibres of the raw coupling. -/
theorem sbxS2_killedFutureRecordLaw_univ_le_one {d : ℕ} (R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d) (ω : FieldPair d) :
    sbxS2KilledFutureRecordLaw R i K ω univ ≤ 1 := by
  classical
  rw [sbxS2KilledFutureRecordLaw,
    Measure.map_apply (sbxS2_measurable_originFutureRecord R i ω) MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ, Probability.probabilityPart_apply]
  split_ifs with h
  · exact (measure_mono (subset_univ _)).trans h.le
  · exact zero_le

/-- The retained environment can be mapped jointly with the sample, so the
literal record measures form a measurable parameter kernel. -/
theorem sbxS2_measurable_killedFutureRecordLaw {d : ℕ} (R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d) : Measurable (sbxS2KilledFutureRecordLaw R i K) := by
  let D : Set (CoupledSample d) := {z | NoBacktracking R z.1 i}
  have hD : MeasurableSet D :=
    (measurableSet_NoBacktracking R i).preimage measurable_fst
  let κ := (Probability.probabilityPart (originCoupledLaw K)).restrict hD
  let recordMap : FieldPair d × CoupledSample d → FutureState d i R :=
    fun p => spatialFutureRecord R i (0, p.1) p.2
  have hrec : Measurable recordMap :=
    (measurable_spatial_future_triple R i).comp
      ((measurable_const.prodMk measurable_fst).prodMk measurable_snd)
  let ν := (Kernel.id ×ₖ κ).map recordMap
  have he : ∀ ω, ν ω = sbxS2KilledFutureRecordLaw R i K ω := by
    intro ω
    apply Measure.ext
    intro S hS
    rw [show ν = (Kernel.id ×ₖ κ).map recordMap from rfl,
      Kernel.map_apply' _ hrec _ hS, Kernel.id_prod_apply' _ _ (hrec hS),
      sbxS2KilledFutureRecordLaw,
      Measure.map_apply (sbxS2_measurable_originFutureRecord R i ω) hS]
    rfl
  exact (funext he) ▸ ν.measurable

/-- The actual full-record kernel, with zero totalization only on exceptional
nonprobability fibres. Its measure on each environment is literal. -/
def sbxS2KilledFutureRecordKernel {d : ℕ} (R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d) : Kernel (FieldPair d) (FutureState d i R) where
  toFun := sbxS2KilledFutureRecordLaw R i K
  measurable' := sbxS2_measurable_killedFutureRecordLaw R i K

/-- Integrating the full record is exactly the source killed-future expectation
on the literal origin-a.e. probability fibres. -/
theorem sbxS2_integral_killedFutureRecordLaw {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) :
    (fun ω => ∫ y, Φ y ∂sbxS2KilledFutureRecordLaw R i K ω) =ᵐ[Q]
      fun ω => ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω) := by
  classical
  filter_upwards [hK.1] with ω hω
  have : IsProbabilityMeasure ((originCoupledLaw K) ω) := hω
  have hm := sbxS2_measurable_originFutureRecord R i ω
  have hD : MeasurableSet {z : CoupledSample d | NoBacktracking R z.1 i} :=
    (measurableSet_NoBacktracking R i).preimage measurable_fst
  rw [sbxS2KilledFutureRecordLaw,
    integral_map hm.aemeasurable hΦ.aestronglyMeasurable,
    Probability.probabilityPart_eq_of_isProbabilityMeasure,
    ← integral_indicator hD]
  rfl

/-- Indicator tests recover the actual masses of the literal killed-record
measure. No locality assertion is used. -/
theorem sbxS2_killedFutureRecordLaw_indicator {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
    (S : Set (FutureState d i R)) (hS : MeasurableSet S) :
    (fun ω => (sbxS2KilledFutureRecordLaw R i K ω S).toReal) =ᵐ[Q]
      fun ω => ∫ z, killedFutureTest R i (S.indicator (fun _ => (1 : ℝ)))
        ((0, ω), z) ∂K (0, ω) := by
  have hΦ : Measurable (S.indicator (fun _ => (1 : ℝ))) :=
    measurable_const.indicator hS
  have h := sbxS2_integral_killedFutureRecordLaw Q K hK R i _ hΦ
  simpa only [integral_indicator_const (1 : ℝ) hS, smul_eq_mul, mul_one,
    Measure.real] using h

/-- For the supplied coupling, full bounded-test locality is equivalent to its
indicator case. Thus the remaining analytic producer is exactly the actual
origin killed-record indicator locality, with both restricted fields retained. -/
theorem sbxS2_future_versions_iff_indicator_versions {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q] (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d) :
    (∀ Φ : FutureState d i R → ℝ, Measurable Φ → BoundedRealTest Φ →
      ∃ B : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | -2 * R ≤ x i}] B ∧
        (fun ω => ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω)) =ᵐ[Q] B) ↔
    (∀ S : Set (FutureState d i R), MeasurableSet S →
      ∃ B : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | -2 * R ≤ x i}] B ∧
        (fun ω => ∫ z, killedFutureTest R i (S.indicator (fun _ => (1 : ℝ)))
          ((0, ω), z) ∂K (0, ω)) =ᵐ[Q] B) := by
  classical
  constructor
  · intro h S hS
    apply h _ (measurable_const.indicator hS)
    refine ⟨1, fun y => ?_⟩
    by_cases hy : y ∈ S
    · simp only [Set.indicator_of_mem hy, abs_one, le_refl]
    · simp only [Set.indicator_of_notMem hy, abs_zero, zero_le_one]
  · intro h Φ hΦ hb
    have hlocal : ∀ S : Set (FutureState d i R), MeasurableSet S →
        ∃ B : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | -2 * R ≤ x i}] B ∧
          (fun ω => (sbxS2KilledFutureRecordLaw R i K ω S).toReal) =ᵐ[Q] B := by
      intro S hS
      obtain ⟨B, hB, he⟩ := h S hS
      exact ⟨B, hB, (sbxS2_killedFutureRecordLaw_indicator Q K hK R i S hS).trans he⟩
    obtain ⟨B, hB, he⟩ := local_kernel_bounded_test_version_of_indicator_versions Q
      (localSigma {x : Vec d | -2 * R ≤ x i}) le_rfl
      (sbxS2KilledFutureRecordLaw R i K) (sbxS2_killedFutureRecordLaw_univ_le_one R i K)
      hlocal Φ hΦ hb
    exact ⟨B, hB, (sbxS2_integral_killedFutureRecordLaw Q K hK R i Φ hΦ).symm.trans he⟩

/-- Stop the path at the fixed future half-space boundary and retain every coin. -/
def sbxS2StopFutureSample {d : ℕ} (R : ℝ) (i : Fin d)
    (z : CoupledSample d) : CoupledSample d :=
  (localityStoppedPath {x : Vec d | -2 * R < x i} z.1, z.2)

theorem sbxS2_measurable_stopFutureSample {d : ℕ} (R : ℝ) (i : Fin d) :
    Measurable (sbxS2StopFutureSample R i) :=
  ((EinsteinFull.measurable_localityStoppedPath _
    (isOpen_lt continuous_const (continuous_apply i))).comp measurable_fst).prodMk
      measurable_snd

/-- The stopped joint path/coin kernel of the supplied coupling. -/
def sbxS2StoppedOriginKernel {d : ℕ} (R : ℝ) (i : Fin d)
    (K : CoupledQuenchedLaws d) : Kernel (FieldPair d) (CoupledSample d) :=
  (Probability.probabilityPart (originCoupledLaw K)).map (sbxS2StopFutureSample R i)

/-- Killing at the inner barrier removes all changes introduced by stopping at
the outer barrier. This is equality of joint path/coin measures, on one common
environment-a.e. set, for the actual supplied coupling. -/
theorem sbxS2_stoppedOriginKernel_restrict_of_coupling {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K)
    (R : ℝ) (hR : 0 < R) (i : Fin d) :
    ∀ᵐ ω ∂Q.measure,
      ((sbxS2StoppedOriginKernel R i K) ω).restrict {z | NoBacktracking R z.1 i} =
        ((Probability.probabilityPart (originCoupledLaw K)) ω).restrict
          {z | NoBacktracking R z.1 i} := by
  classical
  have hD : MeasurableSet {z : CoupledSample d | NoBacktracking R z.1 i} :=
    (measurableSet_NoBacktracking R i).preimage measurable_fst
  filter_upwards [hK.1.1,
    future_locality_ae_starts_at_origin_of_coupling hd Q lam l δ h₀ h₁ P K hK]
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

/-- The entire killed future-record measure factors through the stopped
path/coin kernel, with a common environment-a.e. equality for all record tests. -/
theorem sbxS2_killedFutureRecordLaw_stopped_of_coupling {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l δ : ℝ)
    (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K)
    (R : ℝ) (hR : 0 < R) (i : Fin d) :
    ∀ᵐ ω ∂Q.measure,
      sbxS2KilledFutureRecordLaw R i K ω =
        (((sbxS2StoppedOriginKernel R i K) ω).restrict
          {z | NoBacktracking R z.1 i}).map (spatialFutureRecord R i (0, ω)) := by
  filter_upwards [sbxS2_stoppedOriginKernel_restrict_of_coupling
    hd Q lam l δ h₀ h₁ P K hK R hR i] with ω he
  exact congrArg (Measure.map (spatialFutureRecord R i (0, ω))) he.symm

#print axioms sbxS2_killedFutureRecordLaw_stopped_of_coupling
#print axioms sbxS2StopFutureSample
#print axioms sbxS2_measurable_stopFutureSample
#print axioms sbxS2StoppedOriginKernel
#print axioms sbxS2_stoppedOriginKernel_restrict_of_coupling
#print axioms sbxS2KilledFutureRecordLaw
#print axioms sbxS2_measurable_originFutureRecord
#print axioms sbxS2_killedFutureRecordLaw_univ_le_one
#print axioms sbxS2_measurable_killedFutureRecordLaw
#print axioms sbxS2KilledFutureRecordKernel
#print axioms sbxS2_integral_killedFutureRecordLaw
#print axioms sbxS2_killedFutureRecordLaw_indicator
#print axioms sbxS2_future_versions_iff_indicator_versions
#lint

end EinsteinFull.Blueprint
