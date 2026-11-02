import EinsteinFull.Blueprint.G1.Proofs.SbxS8FutureKernel
import EinsteinRelation.Probability.FiniteHistoryStopping
import EinsteinRelation.Probability.FiniteHistoryExhaustion
import EinsteinRelation.Probability.IncreasingSigmaMeasureExt
import EinsteinRelation.Regeneration.FiniteBarrierLimit
import EinsteinRelation.Environment.FieldMeasurability
import Mathlib.MeasureTheory.Measure.Continuity
import Mathlib.MeasureTheory.SetAlgebra
import Mathlib.Probability.Kernel.Condexp

open MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinRelation.Regeneration

/-- The literal strict barrier through the finite grid horizon. -/
def sbxS8FutureBarrier {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (n : ℕ) :
    Set (CoupledSample d) :=
  {z | ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i}

theorem sbxS8_measurableSet_futureBarrier_history {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (n : ℕ) :
    @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n)
      (sbxS8FutureBarrier Δ R i n) :=
  measurableSet_noBacktracking_prefix Δ n R i

theorem sbxS8_measurableSet_futureBarrier {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (n : ℕ) :
    MeasurableSet (sbxS8FutureBarrier Δ R i n) :=
  Probability.finiteHistorySigma_le Δ n _
    (sbxS8_measurableSet_futureBarrier_history Δ R i n)

theorem sbxS8_futureBarrier_antitone {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) :
    Antitone (sbxS8FutureBarrier Δ R i) := by
  intro m n hmn z hz t ht
  exact hz t (ht.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hmn) zero_le))

/-- Exhausting the grid horizons recovers the strict source event D exactly. -/
theorem sbxS8_iInter_futureBarrier {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ)
    (R : ℝ) (i : Fin d) :
    (⋂ n : ℕ, sbxS8FutureBarrier Δ R i n) = {z | NoBacktracking R z.1 i} := by
  ext z
  simp only [mem_iInter, sbxS8FutureBarrier, mem_ofPred_eq, noBacktracking_iff_forall]
  constructor
  · intro h t
    obtain ⟨n, hn⟩ := exists_nat_ge (t / Δ)
    exact h n t ((div_le_iff₀ hΔ).mp hn)
  · exact fun h _ t _ => h t

/-- Retain the actual path through nΔ and precisely the coins with index < n,
after killing at the finite strict barrier. This is an unnormalized measure. -/
def sbxS8FiniteKilledHistory {d : ℕ} (μ : Measure (CoupledSample d))
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (n : ℕ) : Measure (CoupledSample d) :=
  (μ.restrict (sbxS8FutureBarrier Δ R i n)).map (Probability.stoppedHistorySample Δ n)

/-- The stopped history map is also measurable on the full sample sigma. -/
theorem sbxS8_measurable_stoppedHistorySample {d : ℕ} (Δ : ℝ≥0) (n : ℕ) :
    Measurable (Probability.stoppedHistorySample (d := d) Δ n) :=
  (Probability.measurable_stoppedHistorySample Δ n).mono
    (Probability.finiteHistorySigma_le Δ n) le_rfl

/-- The finite prefix of the actual origin record retains both reduced fields. -/
def sbxS8OriginFuturePrefix {d : ℕ} (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (n : ℕ)
    (p : FieldPair d × CoupledSample d) : FutureState d i R :=
  spatialFutureRecord R i (0, p.1) (Probability.stoppedHistorySample Δ n p.2)

/-- Local measurability of the entire joint origin record. This uses the
physical-to-reduced local sigma transport for both matrix and scalar fields. -/
theorem sbxS8_measurable_originFutureRecord_local {d : ℕ} (R : ℝ) (i : Fin d) :
    @Measurable (FieldPair d × CoupledSample d) (FutureState d i R)
      ((localSigma {x : Vec d | -2 * R ≤ x i}).prod inferInstance) inferInstance
      (fun p => spatialFutureRecord R i (0, p.1) p.2) := by
  let : MeasurableSpace (FieldPair d × CoupledSample d) :=
    (localSigma {x : Vec d | -2 * R ≤ x i}).prod inferInstance
  have hpath : @Measurable (FieldPair d × CoupledSample d) (Path d)
      ((localSigma {x : Vec d | -2 * R ≤ x i}).prod inferInstance) inferInstance
      (fun p => (recenterSample (0 : Vec d) p.2).1) :=
    Probability.continuous_path_recenter.measurable.comp
      (measurable_const.prodMk measurable_snd.fst)
  have hbits : @Measurable (FieldPair d × CoupledSample d) BernoulliSequence
      ((localSigma {x : Vec d | -2 * R ≤ x i}).prod inferInstance) inferInstance
      (fun p => p.2.2) := measurable_snd.snd
  refine hpath.prodMk (hbits.prodMk ?_)
  apply measurable_pi_iff.mpr
  intro x
  have heval : Measurable[localSigma {x : Vec d | -2 * R ≤ x i}]
      (fun ω : FieldPair d => (ω.1 (x : Vec d), ω.2 (x : Vec d))) := by
    apply Measurable.of_comap_le
    exact le_iSup_of_le x le_rfl
  have hred := heval.comp (Probability.measurable_reduce_local {x : Vec d | -2 * R ≤ x i})
  have hf : @Measurable (FieldPair d × CoupledSample d) (FieldPair d)
      ((localSigma {x : Vec d | -2 * R ≤ x i}).prod inferInstance)
      (localSigma {x : Vec d | -2 * R ≤ x i}) Prod.fst := measurable_fst
  simpa only [spatialFutureRecord, translate_zero, Function.comp_def] using hred.comp hf

/-- Joint finite prefixes use the physical future-half-space sigma and the
literal finite path/coin history sigma; the field is never replaced by a. -/
theorem sbxS8_measurable_originFuturePrefix_local {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (n : ℕ) :
    @Measurable (FieldPair d × CoupledSample d) (FutureState d i R)
      ((localSigma {x : Vec d | -2 * R ≤ x i}).prod (finiteHistorySigma Δ n))
      inferInstance (sbxS8OriginFuturePrefix Δ R i n) := by
  let : MeasurableSpace (FieldPair d × CoupledSample d) :=
    (localSigma {x : Vec d | -2 * R ≤ x i}).prod (finiteHistorySigma Δ n)
  have hs : @Measurable (FieldPair d × CoupledSample d) (CoupledSample d)
      ((localSigma {x : Vec d | -2 * R ≤ x i}).prod (finiteHistorySigma Δ n))
      inferInstance (fun p => Probability.stoppedHistorySample Δ n p.2) :=
    (Probability.measurable_stoppedHistorySample Δ n).comp measurable_snd
  exact (sbxS8_measurable_originFutureRecord_local R i).comp (measurable_fst.prodMk hs)

/-- No limit of stopped records is used: only the barrier changes, while the
arbitrary bounded measurable full future test is held fixed. -/
theorem sbxS8_tendsto_integral_futureBarrier {d : ℕ}
    (μ : Measure (CoupledSample d)) [IsFiniteMeasure μ]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (i : Fin d) (ω : FieldPair d)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hb : BoundedRealTest Φ) :
    Tendsto (fun n : ℕ => ∫ z, (sbxS8FutureBarrier Δ R i n).indicator
        (fun z => Φ (spatialFutureRecord R i (0, ω) z)) z ∂μ) atTop
      (𝓝 (∫ z, killedFutureTest R i Φ ((0, ω), z) ∂μ)) := by
  exact tendsto_integral_finite_barrier μ Δ hΔ R i
    (fun z => Φ (spatialFutureRecord R i (0, ω) z))
    (hΦ.comp (sbxS2_measurable_originFutureRecord R i ω))
    ⟨hb.choose, fun z => hb.choose_spec _⟩

/-- Apply the limit on the actual origin probability fibres, preserving the
origin-a.e. qualifier instead of substituting a spatial-a.e. statement. -/
theorem sbxS8_ae_tendsto_integral_futureBarrier {d : ℕ}
    (Q : Measure (FieldPair d)) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) (hb : BoundedRealTest Φ) :
    ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => ∫ z, (sbxS8FutureBarrier Δ R i n).indicator
        (fun z => Φ (spatialFutureRecord R i (0, ω) z)) z ∂K (0, ω)) atTop
      (𝓝 (∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω))) := by
  filter_upwards [hK.1] with ω hp
  have : IsProbabilityMeasure (K (0, ω)) := hp
  exact sbxS8_tendsto_integral_futureBarrier (K (0, ω)) Δ hΔ R i ω Φ hΦ hb

/-- Finite killed-history cylinders determine the complete D-restricted law.
The generating pi-system is the union of the increasing exact history sigmas,
as implemented by `measure_eq_of_increasing_sigma`. Finite-barrier equality
is needed only eventually in the horizon for each earlier-history cylinder. -/
theorem sbxS8_killedMeasure_eq_of_finiteKilledHistory {d : ℕ}
    (μ ν : Measure (CoupledSample d)) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (i : Fin d)
    (hfinite : ∀ n : ℕ, sbxS8FiniteKilledHistory μ Δ R i n =
      sbxS8FiniteKilledHistory ν Δ R i n) :
    μ.restrict {z | NoBacktracking R z.1 i} =
      ν.restrict {z | NoBacktracking R z.1 i} := by
  apply Probability.measure_eq_of_increasing_sigma _ _ (finiteHistorySigma Δ)
    (fun _ _ h => finiteHistorySigma_mono Δ h) (iSup_finiteHistorySigma_eq Δ hΔ)
  intro m s hs
  have hsm : MeasurableSet s := Probability.finiteHistorySigma_le Δ m _ hs
  have hanti : Antitone (fun n => s ∩ sbxS8FutureBarrier Δ R i n) :=
    fun _ _ h => inter_subset_inter_right s (sbxS8_futureBarrier_antitone Δ R i h)
  have hinter : (⋂ n : ℕ, s ∩ sbxS8FutureBarrier Δ R i n) =
      s ∩ {z | NoBacktracking R z.1 i} := by
    rw [← inter_iInter, sbxS8_iInter_futureBarrier Δ hΔ]
  have hμ := tendsto_measure_iInter_atTop
    (fun n => (hsm.inter (sbxS8_measurableSet_futureBarrier Δ R i n)).nullMeasurableSet)
    hanti ⟨0, measure_ne_top μ _⟩
  have hν := tendsto_measure_iInter_atTop
    (fun n => (hsm.inter (sbxS8_measurableSet_futureBarrier Δ R i n)).nullMeasurableSet)
    hanti ⟨0, measure_ne_top ν _⟩
  rw [hinter] at hμ hν
  have heq : (fun n => μ (s ∩ sbxS8FutureBarrier Δ R i n)) =ᶠ[atTop]
      (fun n => ν (s ∩ sbxS8FutureBarrier Δ R i n)) := by
    filter_upwards [eventually_ge_atTop m] with n hn
    have hsn : @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n) s :=
      finiteHistorySigma_mono Δ hn s hs
    rw [Probability.finiteHistorySigma_eq_comap_stopped] at hsn
    obtain ⟨t, ht, hpre⟩ := MeasurableSpace.measurableSet_comap.mp hsn
    have he := congrArg (fun ρ : Measure (CoupledSample d) => ρ t) (hfinite n)
    change ((μ.restrict (sbxS8FutureBarrier Δ R i n)).map
        (Probability.stoppedHistorySample Δ n)) t =
      ((ν.restrict (sbxS8FutureBarrier Δ R i n)).map
        (Probability.stoppedHistorySample Δ n)) t at he
    rw [Measure.map_apply (sbxS8_measurable_stoppedHistorySample Δ n) ht,
      Measure.map_apply (sbxS8_measurable_stoppedHistorySample Δ n) ht, hpre,
      Measure.restrict_apply hsm, Measure.restrict_apply hsm] at he
    exact he
  rw [Measure.restrict_apply hsm, Measure.restrict_apply hsm]
  exact tendsto_nhds_unique (hμ.congr' heq) hν

/-- Pointwise equality of the actual physical field pair on the half-space
identifies both reduced-field components in every origin future record. -/
theorem sbxS8_originFutureRecord_eq_of_local_fields {d : ℕ} (R : ℝ) (i : Fin d)
    (ω ω' : FieldPair d)
    (heq : ∀ x : Vec d, -2 * R ≤ x i → ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x)
    (z : CoupledSample d) :
    spatialFutureRecord R i (0, ω) z = spatialFutureRecord R i (0, ω') z := by
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · rfl
    · funext x
      obtain ⟨ha, hV⟩ := heq x x.property
      simp only [spatialFutureRecord, translate_zero]
      change (Real.exp (-2 * ω.2 x) • ω.1 x, Real.exp (-2 * ω.2 x)) =
        (Real.exp (-2 * ω'.2 x) • ω'.1 x, Real.exp (-2 * ω'.2 x))
      rw [ha, hV]

/-- Push the determined killed measure to the existing complete joint record.
The two actual origin laws, both restricted-field components, and every coin
are retained. There is no equality assertion for unrestricted continuations. -/
theorem sbxS8_killedFutureRecordLaw_eq_of_finiteKilledHistory {d : ℕ}
    (K K' : CoupledQuenchedLaws d) (ω ω' : FieldPair d)
    [IsProbabilityMeasure (K (0, ω))] [IsProbabilityMeasure (K' (0, ω'))]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (i : Fin d)
    (heq : ∀ x : Vec d, -2 * R ≤ x i → ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x)
    (hfinite : ∀ n : ℕ, sbxS8FiniteKilledHistory (K (0, ω)) Δ R i n =
      sbxS8FiniteKilledHistory (K' (0, ω')) Δ R i n) :
    sbxS2KilledFutureRecordLaw R i K ω = sbxS2KilledFutureRecordLaw R i K' ω' := by
  have : IsProbabilityMeasure (originCoupledLaw K ω) :=
    inferInstanceAs (IsProbabilityMeasure (K (0, ω)))
  have : IsProbabilityMeasure (originCoupledLaw K' ω') :=
    inferInstanceAs (IsProbabilityMeasure (K' (0, ω')))
  have hk := sbxS8_killedMeasure_eq_of_finiteKilledHistory
    (K (0, ω)) (K' (0, ω')) Δ hΔ R i hfinite
  have hr : spatialFutureRecord R i (0, ω) = spatialFutureRecord R i (0, ω') :=
    funext (sbxS8_originFutureRecord_eq_of_local_fields R i ω ω' heq)
  unfold sbxS2KilledFutureRecordLaw
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω,
    Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K') ω']
  change ((K (0, ω)).restrict {z | NoBacktracking R z.1 i}).map
      (spatialFutureRecord R i (0, ω)) =
    ((K' (0, ω')).restrict {z | NoBacktracking R z.1 i}).map
      (spatialFutureRecord R i (0, ω'))
  rw [hk, hr]

/-- Fibrewise integral identity for the existing complete record measure. -/
theorem sbxS8_integral_killedFutureRecordLaw {d : ℕ} (K : CoupledQuenchedLaws d)
    (ω : FieldPair d) [IsProbabilityMeasure (K (0, ω))] (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) :
    (∫ y, Φ y ∂sbxS2KilledFutureRecordLaw R i K ω) =
      ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω) := by
  have : IsProbabilityMeasure (originCoupledLaw K ω) :=
    inferInstanceAs (IsProbabilityMeasure (K (0, ω)))
  have hD : MeasurableSet {z : CoupledSample d | NoBacktracking R z.1 i} :=
    (measurableSet_NoBacktracking R i).preimage measurable_fst
  rw [sbxS2KilledFutureRecordLaw,
    Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω,
    integral_map (sbxS2_measurable_originFutureRecord R i ω).aemeasurable
      hΦ.aestronglyMeasurable, ← integral_indicator hD]
  rfl

/-- Finite killed histories compare arbitrary full joint measurable observables
by equality of measures, without pointwise approximation of the observable. -/
theorem sbxS8_integral_killedFutureTest_eq_of_finiteKilledHistory {d : ℕ}
    (K K' : CoupledQuenchedLaws d) (ω ω' : FieldPair d)
    [IsProbabilityMeasure (K (0, ω))] [IsProbabilityMeasure (K' (0, ω'))]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (i : Fin d)
    (heq : ∀ x : Vec d, -2 * R ≤ x i → ω.1 x = ω'.1 x ∧ ω.2 x = ω'.2 x)
    (hfinite : ∀ n : ℕ, sbxS8FiniteKilledHistory (K (0, ω)) Δ R i n =
      sbxS8FiniteKilledHistory (K' (0, ω')) Δ R i n)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ) :
    (∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω)) =
      ∫ z, killedFutureTest R i Φ ((0, ω'), z) ∂K' (0, ω') := by
  rw [← sbxS8_integral_killedFutureRecordLaw K ω R i Φ hΦ,
    ← sbxS8_integral_killedFutureRecordLaw K' ω' R i Φ hΦ,
    sbxS8_killedFutureRecordLaw_eq_of_finiteKilledHistory K K' ω ω' Δ hΔ R i heq hfinite]

/-- Countably many finite-history comparisons give equality of the full record
measures on one common origin-a.e. set, before choosing any full observable. -/
theorem sbxS8_ae_killedFutureRecordLaw_eq_of_finiteKilledHistory {d : ℕ}
    (Q : Measure (FieldPair d)) (K K' : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q K) (hK' : HasProbabilityLaws Q K')
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (i : Fin d)
    (hfinite : ∀ n : ℕ, ∀ᵐ ω ∂Q,
      sbxS8FiniteKilledHistory (K (0, ω)) Δ R i n =
        sbxS8FiniteKilledHistory (K' (0, ω)) Δ R i n) :
    sbxS2KilledFutureRecordLaw R i K =ᵐ[Q] sbxS2KilledFutureRecordLaw R i K' := by
  have hall : ∀ᵐ ω ∂Q, ∀ n : ℕ,
      sbxS8FiniteKilledHistory (K (0, ω)) Δ R i n =
        sbxS8FiniteKilledHistory (K' (0, ω)) Δ R i n := ae_all_iff.mpr hfinite
  filter_upwards [hK.1, hK'.1, hall] with ω hp hp' hn
  have : IsProbabilityMeasure (K (0, ω)) := hp
  have : IsProbabilityMeasure (K' (0, ω)) := hp'
  exact sbxS8_killedFutureRecordLaw_eq_of_finiteKilledHistory K K' ω ω Δ hΔ R i
    (fun _ _ => ⟨rfl, rfl⟩) hn

/-- Consume the checked stopping transport for two literal couplings of the
same supplied path law. Finite killed-history comparison of their stopped
kernels determines the actual full record on one common environment-a.e. set.
This consumer does not produce the finite-history comparison. -/
theorem sbxS8_ae_killedFutureRecordLaw_eq_of_finiteStoppedKilledHistory
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K K' : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K)
    (hK' : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K')
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (hR : 0 < R) (i : Fin d)
    (hfinite : ∀ n : ℕ, ∀ᵐ ω ∂Q.measure,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω) Δ R i n =
        sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K' ω) Δ R i n) :
    sbxS2KilledFutureRecordLaw R i K =ᵐ[Q.measure]
      sbxS2KilledFutureRecordLaw R i K' := by
  have hall : ∀ᵐ ω ∂Q.measure, ∀ n : ℕ,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω) Δ R i n =
        sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K' ω) Δ R i n :=
    ae_all_iff.mpr hfinite
  filter_upwards [hall,
    sbxS2_killedFutureRecordLaw_stopped_of_coupling hd Q lam l δ h₀ h₁ P K hK R hR i,
    sbxS2_killedFutureRecordLaw_stopped_of_coupling hd Q lam l δ h₀ h₁ P K' hK' R hR i]
    with ω hn he he'
  have : IsFiniteMeasure (sbxS2StoppedOriginKernel R i K ω) := by
    unfold sbxS2StoppedOriginKernel
    infer_instance
  have : IsFiniteMeasure (sbxS2StoppedOriginKernel R i K' ω) := by
    unfold sbxS2StoppedOriginKernel
    infer_instance
  rw [he, he', sbxS8_killedMeasure_eq_of_finiteKilledHistory
    (sbxS2StoppedOriginKernel R i K ω) (sbxS2StoppedOriginKernel R i K' ω)
    Δ hΔ R i hn]

attribute [local instance] ReductionImageV3.fieldPair_standardBorel

/-- Invariance of the actual killed path/coin kernel under conditional
resampling gives scalar local versions by conditional averaging. -/
theorem sbxS8_killedPathBit_versions_of_resampling_kernel_eq {d : ℕ}
    (Q : Measure (FieldPair d)) [IsFiniteMeasure Q]
    (K : CoupledQuenchedLaws d) (hK : HasProbabilityLaws Q K) (R : ℝ) (i : Fin d)
    (hκeq : ∀ᵐ ω ∂Q,
      ∀ᵐ ω' ∂condExpKernel Q (localSigma {x : Vec d | -2 * R ≤ x i}) ω,
        sbxS8KilledPathBitKernel R i K ω = sbxS8KilledPathBitKernel R i K ω') :
    HasKilledPathBitFutureVersions Q i R K := by
  intro F hF _hbF
  let f : FieldPair d → ℝ := fun ω => ∫ z, F z ∂sbxS8KilledPathBitKernel R i K ω
  have hf : Measurable f :=
    (hF.stronglyMeasurable.integral_kernel (κ := sbxS8KilledPathBitKernel R i K)).measurable
  have havg : (fun ω => ∫ ω', f ω'
      ∂condExpKernel Q (localSigma {x : Vec d | -2 * R ≤ x i}) ω) =ᵐ[Q] f := by
    filter_upwards [hκeq] with ω hω
    calc
      _ = ∫ _ω', f ω ∂condExpKernel Q (localSigma {x : Vec d | -2 * R ≤ x i}) ω := by
        apply integral_congr_ae
        filter_upwards [hω] with ω' he
        exact congrArg (fun μ : Measure (CoupledSample d) => ∫ z, F z ∂μ) he.symm
      _ = f ω := by simp only [integral_const, probReal_univ, one_smul]
  exact ⟨fun ω => ∫ ω', f ω'
      ∂condExpKernel Q (localSigma {x : Vec d | -2 * R ≤ x i}) ω,
    hf.stronglyMeasurable.integral_condExpKernel.measurable,
    havg.trans (sbxS8_integral_killedPathBitKernel Q K hK R i F)⟩

/-- For the literal supplied coupling, finite killed histories of the stopped
kernel under conditional resampling suffice. Stopping transport is used only
on the killed measure and on a common a.e. set for both conditional copies. -/
theorem sbxS8_killedPathBit_versions_of_resampling_finiteStoppedKilledHistory
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam l δ : ℝ) (h₀ : 0 ≤ lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀ h₁ P K)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (hR : 0 < R) (i : Fin d)
    (hfinite : ∀ n : ℕ, ∀ᵐ ω ∂Q.measure,
      ∀ᵐ ω' ∂condExpKernel Q.measure (localSigma {x : Vec d | -2 * R ≤ x i}) ω,
        sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω) Δ R i n =
          sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω') Δ R i n) :
    HasKilledPathBitFutureVersions Q.measure i R K := by
  let m := localSigma {x : Vec d | -2 * R ≤ x i}
  let : MeasurableSpace (FieldPair d) := borel (FieldPair d)
  have hm := Probability.localSigma_le_borel {x : Vec d | -2 * R ≤ x i}
  have hstop := sbxS8_killedPathBitKernel_stopped_of_coupling
    hd Q lam l δ h₀ h₁ P K hK R hR i
  have hcopies : ∀ᵐ ω ∂Q.measure, ∀ᵐ ω' ∂condExpKernel Q.measure m ω,
      sbxS8KilledPathBitKernel R i K ω' =
        (sbxS2StoppedOriginKernel R i K ω').restrict
          {z | NoBacktracking R z.1 i} := by
    have hc : ∀ᵐ ω' ∂condExpKernel Q.measure m ∘ₘ Q.measure.trim hm,
        sbxS8KilledPathBitKernel R i K ω' =
          (sbxS2StoppedOriginKernel R i K ω').restrict
            {z | NoBacktracking R z.1 i} := by
      rw [condExpKernel_comp_trim hm]
      exact hstop
    exact ae_of_ae_trim hm (Measure.ae_ae_of_ae_comp hc)
  have hall : ∀ᵐ ω ∂Q.measure, ∀ᵐ ω' ∂condExpKernel Q.measure m ω, ∀ n : ℕ,
      sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω) Δ R i n =
        sbxS8FiniteKilledHistory (sbxS2StoppedOriginKernel R i K ω') Δ R i n := by
    filter_upwards [ae_all_iff.mpr hfinite] with ω hω
    exact ae_all_iff.mpr hω
  apply sbxS8_killedPathBit_versions_of_resampling_kernel_eq Q.measure K hK.1 R i
  filter_upwards [hstop, hcopies, hall] with ω hs hc hn
  filter_upwards [hc, hn] with ω' hs' hnn
  have : IsFiniteMeasure (sbxS2StoppedOriginKernel R i K ω) := by
    unfold sbxS2StoppedOriginKernel
    infer_instance
  have : IsFiniteMeasure (sbxS2StoppedOriginKernel R i K ω') := by
    unfold sbxS2StoppedOriginKernel
    infer_instance
  rw [hs, hs']
  exact sbxS8_killedMeasure_eq_of_finiteKilledHistory
    (sbxS2StoppedOriginKernel R i K ω) (sbxS2StoppedOriginKernel R i K ω')
    Δ hΔ R i hnn

end EinsteinFull.Blueprint
