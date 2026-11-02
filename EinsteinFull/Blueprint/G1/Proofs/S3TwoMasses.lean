import EinsteinFull.Blueprint.G1.node_rt_u3A_two_u2D_masses
import EinsteinFull.Blueprint.Foundation.node_rt_u3A_renewal_u23_tube_u2D_probability
import EinsteinFull.Blueprint.Foundation.node_rt_u3A_renewal_u23_tube_u2D_geometry
import EinsteinFull.Blueprint.Foundation.node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transfer
import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_endpoint_u2D_disintegration
import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinRelation.Regeneration.NoBacktrackingPrefix
import EinsteinRelation.Regeneration.FiniteHistoryTrialEvent
import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini
import EinsteinRelation.Regeneration.FreshEventMass
import EinsteinRelation.Regeneration.EndpointBallVolume
import EinsteinRelation.Regeneration.RenewalRecordIteration
import EinsteinRelation.Regeneration.Chronology

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation
open EinsteinRelation.Regeneration (CoupledSample sampleTimeShift pathTimeShift
  forcedBitTrialEvent NoBacktracking finiteHistorySigma firstRegenerationTime forceSampleBit)

/-! # `rt:two-masses`

The conditional lattice mass at `n` equals `δ` times the annealed mass of the prebridge
event with survival; the two tube events supply the lower bound. -/

theorem roundedCandidateSequence_zero_le {d : ℕ} (Δ : ℝ≥0) (lam R a : ℝ)
    (z : CoupledSample d) (i : Fin d) (n : ℕ) :
    Regeneration.roundedCandidateSequence Δ lam R a z i 0 ≤
      Regeneration.roundedCandidateSequence Δ lam R a z i n := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    refine ih.trans ?_
    by_cases h : Regeneration.roundedCandidateSequence Δ lam R a z i n = ⊤
    · rw [Regeneration.roundedCandidateSequence]
      rw [if_pos h]
      exact le_top
    · rw [Regeneration.roundedCandidateSequence]
      rw [if_neg h]
      exact le_self_add

theorem mem_forcedBitTrialEvent_of_candidate {d : ℕ} (Δ : ℝ≥0) (hΔ : 0 < Δ) (lam R : ℝ)
    (i : Fin d) (m : ℕ) (z : CoupledSample d)
    (hc : Regeneration.firstRoundedCandidate Δ lam R (3 * lam * R) z.1 i =
      (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)) :
    z ∈ forcedBitTrialEvent Δ lam R i m := by
  refine ⟨0, ?_⟩
  have h0 : Regeneration.roundedCandidateSequence Δ lam R (3 * lam * R) (forceSampleBit m z) i 0 =
      (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := hc
  have hfs : Regeneration.firstSuccessfulCandidate Δ lam R (3 * lam * R) (forceSampleBit m z) i =
      (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) := by
    apply le_antisymm
    · have hS : Regeneration.IsSuccessfulCandidate Δ lam R (3 * lam * R) (forceSampleBit m z) i 0 := by
        unfold Regeneration.IsSuccessfulCandidate
        dsimp only
        refine ⟨by rw [h0]; exact ENNReal.coe_ne_top, ?_⟩
        rw [h0, ENNReal.toNNReal_coe, Regeneration.gridIndex_mul Δ hΔ]
        simp [forceSampleBit]
      exact iInf_le_of_le 0 (iInf_le_of_le hS h0.le)
    · refine le_iInf fun n => le_iInf fun _ => ?_
      rw [← h0]
      exact roundedCandidateSequence_zero_le _ _ _ _ _ _ n
  rw [Regeneration.trialStartSequence, hfs, ← ENNReal.coe_add]
  congr 1
  push_cast
  ring

/-- The annealed mass of a sample event is at least a constant that bounds its quenched
origin masses from below. -/
theorem annealed_mass_lower {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Regeneration.CoupledQuenchedLaws d) (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (T : Set (CoupledSample d)) (hT : MeasurableSet T) (c : ℝ≥0∞)
    (h : ∀ᵐ ω ∂Q.measure, c ≤ K (0, ω) T) :
    c ≤ Regeneration.annealedCoupledLaw Q.measure K {q | q.2 ∈ T} := by
  have hm : MeasurableSet {q : FieldPair d × CoupledSample d | q.2 ∈ T} := measurable_snd hT
  unfold Regeneration.annealedCoupledLaw
  rw [Measure.compProd_apply hm]
  calc c = ∫⁻ _ω, c ∂Q.measure := by simp
    _ ≤ _ := by
      apply lintegral_mono_ae
      filter_upwards [h, hK.1] with ω hω hp
      haveI : IsProbabilityMeasure (Regeneration.originCoupledLaw K ω) := hp
      rw [Probability.probabilityPart_eq_of_isProbabilityMeasure
        (Regeneration.originCoupledLaw K) ω]
      exact hω

/-- The conditional lattice mass in terms of the unconditioned slice integral of the
survival indicator. -/
theorem lattice_mass_formula {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ₀ : 0 < δ) (hδ₁ : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hdisint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    (n : ℕ) (hn : 2 ≤ n) :
    regenerationLatticeMass hd Q lam l K hK.1 hD n =
      δ * (Regeneration.annealedCoupledLaw Q.measure K {q | q.2 ∈
        forcedBitTrialEvent (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) (n - 1) ∩
        {z | ∀ t : ℝ≥0, t ≤ ((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam →
          -(l / lam) < z.1 t (Regeneration.Renewal.forceCoord hd) -
            z.1 0 (Regeneration.Renewal.forceCoord hd)}}).toReal := by
  classical
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl h₀
  haveI hμ : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let S : Set (CoupledSample d) :=
    {z | ∀ t : ℝ≥0, t ≤ ((n - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam →
      -(l / lam) < z.1 t (Regeneration.Renewal.forceCoord hd) -
        z.1 0 (Regeneration.Renewal.forceCoord hd)}
  have hSσ : @MeasurableSet (CoupledSample d)
      (finiteHistorySigma (Regeneration.Renewal.regenDelta lam) (n - 1)) S :=
    Regeneration.measurableSet_noBacktracking_prefix _ _ _ _
  have hSm : MeasurableSet S :=
    (Probability.finiteHistorySigma_le (d := d) (Regeneration.Renewal.regenDelta lam) (n - 1))
      _ hSσ
  let H : CoupledSample d → ℝ := S.indicator (fun _ => 1)
  have hH : @Measurable (CoupledSample d) ℝ
      (finiteHistorySigma (Regeneration.Renewal.regenDelta lam) (n - 1)) inferInstance H :=
    Measurable.indicator measurable_const hSσ
  have hbH : Regeneration.BoundedRealTest H := ⟨1, fun z => by
    by_cases hz : z ∈ S <;> simp [H, hz]⟩
  let Gm := forcedBitTrialEvent (Regeneration.Renewal.regenDelta lam) lam (l / lam)
    (Regeneration.Renewal.forceCoord hd) (n - 1)
  have hGm : MeasurableSet Gm :=
    Regeneration.measurableSet_forcedBitTrialEvent _ _ _ _ _
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let D := regenerationNoReturn hd (l / lam)
  have hDm : MeasurableSet D :=
    (Regeneration.measurableSet_NoBacktracking (l / lam) (Regeneration.Renewal.forceCoord hd)).preimage
      measurable_snd.fst
  let slice : Set (FieldPair d × CoupledSample d) := {q | regenerationTime hd lam l 1 q.2 =
    (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)}
  have hslice : MeasurableSet slice := by
    have ht (z : CoupledSample d) : regenerationTime hd lam l 1 z =
        firstRegenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) z
          (Regeneration.Renewal.forceCoord hd) := Regeneration.regenerationTime_one _ _ _ _ _
    simp only [slice, ht]
    exact ((Regeneration.measurable_firstRegenerationTime (Regeneration.Renewal.regenDelta lam) lam
      (l / lam) (Regeneration.Renewal.forceCoord hd)).comp measurable_snd)
      (measurableSet_singleton _)
  let S' : Set (FieldPair d × CoupledSample d) := {q | q.2 ∈ S}
  have hS' : MeasurableSet S' := measurable_snd hSm
  -- endpoint disintegration with trivial future test
  have hdis := hdisint d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK
    (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩ n hn H hH hbH
    (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩
    (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩
  -- independence for the trivial future test
  obtain ⟨-, ha, hb, hc, -⟩ := (hindep d hd Λ₀ r₀ Q lam h₀ h₁ l δ hl hsep hδ₀ hδ₁ P K hK hD
    (fun _ => (1 : ℝ) * 1) measurable_const ⟨1, fun _ => by norm_num⟩).1
    (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩ n hn H hH hbH
  let A : Vec d → FieldPair d → ℝ := fun y ω =>
    Regeneration.firstSlicePastIntegral (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) (n - 1) K H (y, ω)
  let B : Vec d → FieldPair d → ℝ := fun y ω =>
    ∫ z, Regeneration.killedFutureTest (l / lam) (Regeneration.Renewal.forceCoord hd)
      (fun _ => (1 : ℝ)) ((y, ω), z) ∂K (y, ω)
  have hDreal : (∫ q in D, (1 : ℝ) * 1 ∂μ) = μ.real D := by
    simp
  have hAB : ∀ᵐ y ∂(volume : Measure (Vec d)),
      (∫ ω, A y ω * B y ω ∂Q.measure) = (∫ ω, A y ω ∂Q.measure) * μ.real D := by
    filter_upwards [ha, hb, hc] with y hay hby hcy
    by_cases hy : y (Regeneration.Renewal.forceCoord hd) < 10 * (l / lam)
    · have h0 := hay hy
      have e1 : (fun ω => A y ω * B y ω) =ᵐ[Q.measure] 0 := by
        filter_upwards [h0] with ω hω
        have : A y ω = 0 := by simpa [A] using hω
        simp [this]
      have e2 : (fun ω => A y ω) =ᵐ[Q.measure] 0 := by
        filter_upwards [h0] with ω hω
        simpa [A] using hω
      rw [integral_congr_ae e1, integral_congr_ae e2]
      simp
    · have h1 := (hby (not_lt.mp hy)).2
      have h2 : (∫ ω, B y ω ∂Q.measure) = μ.real D := by
        have := hcy
        simp only [mul_one] at this
        simpa [B, hDreal] using this
      have h2' := h2
      simp only [B, one_mul] at h2'
      simp only [A, B, one_mul] at h1 ⊢
      rw [h1, h2']
  have hsum : (∫ y, ∫ ω, A y ω * B y ω ∂Q.measure) =
      μ.real D * ∫ y, ∫ ω, A y ω ∂Q.measure := by
    rw [← integral_const_mul]
    exact integral_congr_ae (hAB.mono fun y hy => by dsimp only; rw [hy]; ring)
  -- the spatial integral of the past factor
  let G : CoupledSample d → ℝ := Gm.indicator H
  have hGmeas : Measurable G :=
    (hH.mono (Probability.finiteHistorySigma_le (d := d)
      (Regeneration.Renewal.regenDelta lam) (n - 1)) le_rfl).indicator hGm
  have hbG : Regeneration.BoundedRealTest G := ⟨1, fun z => by
    by_cases hz : z ∈ Gm <;> by_cases hz' : z ∈ S <;> simp [G, H, hz, hz']⟩
  have hvol : 0 < (volume (Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd)
      (l / lam) (0 : Vec d))).toReal :=
    ENNReal.toReal_pos (Regeneration.endpointBall_volume_pos _ _ hR 0).ne'
      (Regeneration.endpointBall_volume_ne_top _ _ hR 0)
  have hea : ∀ x : Vec d, Regeneration.endpointAverage (Regeneration.Renewal.forceCoord hd)
      (l / lam) x (fun _ => (1 : ℝ)) = 1 := by
    intro x
    unfold Regeneration.endpointAverage
    rw [setIntegral_const, smul_eq_mul, mul_one, measureReal_def,
      Regeneration.endpointBall_volume_eq]
    exact div_self hvol.ne'
  have hfub := Regeneration.integral_annealed_endpointAverage_fubini Q.measure K hK.1
    (Regeneration.Renewal.regenDelta lam) (n - 1) (Regeneration.Renewal.forceCoord hd) (l / lam)
    hR G hGmeas hbG (fun _ => (1 : ℝ)) measurable_const ⟨1, fun _ => by norm_num⟩
  simp only [hea, mul_one] at hfub
  let GS : Set (FieldPair d × CoupledSample d) := {q | q.2 ∈ Gm ∩ S}
  have hGS : MeasurableSet GS := measurable_snd (hGm.inter hSm)
  have hLHS : (∫ ω, ∫ z, G z ∂K (0, ω) ∂Q.measure) = μ.real GS := by
    have h1 := Regeneration.integral_annealedCoupledLaw Q.measure K hK.1
      (fun q => G q.2) (hGmeas.comp measurable_snd)
      ⟨1, fun q => by by_cases hz : q.2 ∈ Gm <;> by_cases hz' : q.2 ∈ S <;>
        simp [G, H, hz, hz']⟩
    have h2 : (fun q : FieldPair d × CoupledSample d => G q.2) =
        GS.indicator (fun _ => (1 : ℝ)) := by
      funext q
      by_cases hz : q.2 ∈ Gm <;> by_cases hz' : q.2 ∈ S <;>
        simp [G, H, GS, hz, hz']
    rw [← h1, h2, integral_indicator_const _ hGS, smul_eq_mul, mul_one]
  have hAint : (∫ y, ∫ ω, A y ω ∂Q.measure) =
      (volume (Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd)
        (l / lam) (0 : Vec d))).toReal * μ.real GS := by
    have hX : (∫ y, ∫ ω, A y ω ∂Q.measure) =
        (volume (Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd)
          (l / lam) (0 : Vec d))).toReal * ∫ ω, ∫ z, G z ∂K (0, ω) ∂Q.measure := by
      rw [hfub, ← mul_assoc, mul_inv_cancel₀ hvol.ne', one_mul]
      try rfl
    rw [hX, hLHS]
  have hdis2 : (∫ q in slice, H q.2 ∂μ) =
      δ / (volume (Regeneration.endpointBall (Regeneration.Renewal.forceCoord hd)
        (l / lam) (0 : Vec d))).toReal * ∫ y, ∫ ω, A y ω * B y ω ∂Q.measure := by
    dsimp only at hdis
    simp only [one_mul, mul_one] at hdis
    exact hdis
  have hμD : 0 < μ.real D := ENNReal.toReal_pos hD (measure_ne_top _ _)
  have hfin1 : (∫ q in slice, H q.2 ∂μ) = δ * μ.real D * μ.real GS := by
    have hv := hvol.ne'
    rw [hdis2, hsum, hAint]
    field_simp
  -- identification of the conditioned mass
  have ht (z : CoupledSample d) : regenerationTime hd lam l 1 z =
      firstRegenerationTime (Regeneration.Renewal.regenDelta lam) lam (l / lam) z
        (Regeneration.Renewal.forceCoord hd) := Regeneration.regenerationTime_one _ _ _ _ _
  have hae := Regeneration.ae_noBacktracking_iff_prefix_on_firstRegenerationSlice Q.measure K
    hK.1 (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam) h₀ hR
    (Regeneration.Renewal.forceCoord hd) (n - 1) hK.2.2.2.2.2.1
  rw [Nat.sub_add_cancel (by omega : 1 ≤ n)] at hae
  have h3 : μ (D ∩ slice) = μ (S' ∩ slice) := by
    apply measure_congr
    refine Filter.eventuallyEq_set.mpr (hae.mono fun q hq => ?_)
    constructor
    · rintro ⟨h1, h2⟩
      have h2' := h2
      simp only [slice, Set.mem_setOf_eq, ht] at h2'
      exact ⟨(hq h2').mp h1, h2⟩
    · rintro ⟨h1, h2⟩
      have h2' := h2
      simp only [slice, Set.mem_setOf_eq, ht] at h2'
      exact ⟨(hq h2').mpr h1, h2⟩
  have h4 : (∫ q in slice, H q.2 ∂μ) = (μ (S' ∩ slice)).toReal := by
    have e : (fun q : FieldPair d × CoupledSample d => H q.2) =
        S'.indicator (fun _ => (1 : ℝ)) := by
      funext q
      by_cases hz : q.2 ∈ S <;> simp [H, S', hz]
    rw [e, integral_indicator_const _ hS', smul_eq_mul, mul_one, measureReal_def,
      Measure.restrict_apply hS']
  show (ProbabilityTheory.cond μ D).real slice = δ * (μ GS).toReal
  rw [measureReal_def, ProbabilityTheory.cond_apply hDm, ENNReal.toReal_mul,
    ENNReal.toReal_inv, h3, ← h4, hfin1]
  have : (μ D).toReal = μ.real D := rfl
  rw [this]
  change (μ.real D)⁻¹ * (δ * μ.real D * μ.real GS) = δ * μ.real GS
  have hμD' := hμD.ne'
  field_simp

/-- A positive-force coupling at scale `l` has a first-cycle mass at lattice points two
and three bounded below. -/
@[nolint unusedArguments]
theorem node_rt_u3A_two_u2D_masses_of_deps
    (_htubeProb : node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt)
    (hdisint : node_app_u3A_factorization_u23_endpoint_u2D_disintegrationStmt)
    (hindep : node_app_u3A_factorization_u23_independenceStmtV2)
    (hgeom : node_rt_u3A_renewal_u23_tube_u2D_geometryStmt)
    (htransfer : node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transferStmt) :
    node_rt_u3A_two_u2D_massesStmt := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hr₀, hT⟩ := htransfer d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hr₀, ?_⟩
  intro l hl δ hδ₀ hδ₁
  obtain ⟨cD, c, C, η, N, hcD, hc, hC, hη, hη1, hN, hfun⟩ := hT l hl δ hδ₀ hδ₁
  refine ⟨δ * η ^ N, by positivity, ?_⟩
  intro Q lam h₀ h₁ P K hK hD
  have hl0 : 0 < l := hl₀.trans_le hl
  have hsepl : r₀ < 2 * l := by linarith
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h₀))
  have hR : 0 < l / lam := div_pos hl0 h₀
  have hex := (hfun Q lam h₀ h₁ P K hK).2.2
  have hstart : ∀ᵐ ω ∂Q.measure, ∀ᵐ z ∂K (0, ω), z.1 0 = 0 := by
    filter_upwards [hK.2.1.1, hK.2.2.1] with ω hm hP
    obtain ⟨_, r, hr⟩ := hP
    have hs : ∀ᵐ γ ∂P (0, ω), γ 0 = 0 := by
      rw [hr 0]
      exact r.pathLaw_starts_at 0
    rw [← hm] at hs
    exact ae_of_ae_map measurable_fst.aemeasurable hs
  have key : ∀ j : ℕ, (j = 2 ∨ j = 3) →
      δ * η ^ N ≤ regenerationLatticeMass hd Q lam l K hK.1 hD j := by
    intro j hj
    have hn : 2 ≤ j := by rcases hj with rfl | rfl <;> norm_num
    rw [lattice_mass_formula hd Q lam h₀ h₁ l δ hl0 hsepl hδ₀ hδ₁ P K hK hD hdisint hindep j hn]
    haveI hμ : IsProbabilityMeasure (Regeneration.annealedCoupledLaw Q.measure K) :=
      Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
    let S : Set (CoupledSample d) :=
      {z | ∀ t : ℝ≥0, t ≤ ((j - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam →
        -(l / lam) < z.1 t (Regeneration.Renewal.forceCoord hd) -
          z.1 0 (Regeneration.Renewal.forceCoord hd)}
    have hSσ : @MeasurableSet (CoupledSample d)
        (finiteHistorySigma (Regeneration.Renewal.regenDelta lam) (j - 1)) S :=
      Regeneration.measurableSet_noBacktracking_prefix _ _ _ _
    have hSm : MeasurableSet S :=
      (Probability.finiteHistorySigma_le (d := d) (Regeneration.Renewal.regenDelta lam) (j - 1))
        _ hSσ
    let Gm := forcedBitTrialEvent (Regeneration.Renewal.regenDelta lam) lam (l / lam)
      (Regeneration.Renewal.forceCoord hd) (j - 1)
    have hGm : MeasurableSet Gm :=
      Regeneration.measurableSet_forcedBitTrialEvent _ _ _ _ _
    have hGmσ : @MeasurableSet (CoupledSample d)
        (finiteHistorySigma (Regeneration.Renewal.regenDelta lam) (j - 1)) Gm :=
      Regeneration.measurableSet_forcedBitTrialEvent_finiteHistory _ hΔ lam (l / lam) hR _ _
    have hAσ : @MeasurableSet (CoupledSample d)
        (finiteHistorySigma (Regeneration.Renewal.regenDelta lam) (j - 1)) (Gm ∩ S) :=
      @MeasurableSet.inter _ (finiteHistorySigma (Regeneration.Renewal.regenDelta lam) (j - 1))
        _ _ hGmσ hSσ
    have hfresh := Regeneration.measure_annealed_fresh_bit Q.measure K hK.1
      (Regeneration.Renewal.regenDelta lam) δ hδ₀.le hK.2.2.2.1 (j - 1) (Gm ∩ S) hAσ
    have hcoin : MeasurableSet {z : CoupledSample d | z.2 (j - 1) = true} :=
      measurableSet_eq_fun ((measurable_pi_apply (j - 1)).comp measurable_snd) measurable_const
    have hlow : ENNReal.ofReal (δ * η ^ N) ≤ Regeneration.annealedCoupledLaw Q.measure K
        {q | q.2 ∈ (Gm ∩ S) ∩ {z : CoupledSample d | z.2 (j - 1) = true}} := by
      apply annealed_mass_lower Q K hK.1 _ ((hGm.inter hSm).inter hcoin)
      filter_upwards [hex, hstart] with ω hω hs0
      refine ((hω j hj).2).trans (measure_mono_ae ?_)
      filter_upwards [hs0] with z hz0 hz
      obtain ⟨hzE, hzc⟩ := hz
      obtain ⟨-, -, -, hfirst, hsurv⟩ := hgeom d hd l hl0 lam h₀ h₁ j hj z.1 hz0 hzE
      have hfirst' : Regeneration.firstRoundedCandidate (Regeneration.Renewal.regenDelta lam) lam
          (l / lam) (3 * lam * (l / lam)) z.1 (Regeneration.Renewal.forceCoord hd) =
          ((((j - 1 : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞) := by
        rw [hfirst]; norm_cast
      refine ⟨⟨mem_forcedBitTrialEvent_of_candidate _ hΔ lam (l / lam) _ (j - 1) z hfirst', ?_⟩,
        hzc⟩
      intro t ht
      have h1 := hsurv t ht
      have e : z.1 0 (Regeneration.Renewal.forceCoord hd) = 0 := by rw [hz0]; rfl
      rw [e]
      linarith
    have hfresh' : (Regeneration.annealedCoupledLaw Q.measure K
        {q | q.2 ∈ (Gm ∩ S) ∩ {z : CoupledSample d | z.2 (j - 1) = true}}) =
        ENNReal.ofReal δ * Regeneration.annealedCoupledLaw Q.measure K {q | q.2 ∈ Gm ∩ S} :=
      hfresh
    rw [hfresh'] at hlow
    have hfin : Regeneration.annealedCoupledLaw Q.measure K {q | q.2 ∈ Gm ∩ S} ≠ ⊤ :=
      measure_ne_top _ _
    have := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hfin) hlow
    rw [ENNReal.toReal_ofReal (by positivity), ENNReal.toReal_mul,
      ENNReal.toReal_ofReal hδ₀.le] at this
    exact this
  exact ⟨key 2 (Or.inl rfl), key 3 (Or.inr rfl)⟩

end EinsteinFull.Blueprint
