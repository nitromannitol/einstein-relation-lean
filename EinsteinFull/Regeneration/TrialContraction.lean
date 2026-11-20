import EinsteinFull.Regeneration.TrialHistory
import EinsteinFull.Regeneration.CandidateConstants
import EinsteinFull.Regeneration.TrialMomentRecurrence
import EinsteinFull.Regeneration.SmallTiltContraction
import EinsteinFull.Regeneration.FinitenessFromPositiveExit
import EinsteinFull.Regeneration.TailFromPositiveExit

/-!
# Contraction of the weighted trial starts

The exponential height of the next trial start is at most the exponential height of
the current trial start times the failure factor of a trial and the moment factor of a
candidate search. At a small exponent the product is below one, which gives the
exponential moment of the first regeneration endpoint (GMP (5.26), following the
geometric argument of Shen, Theorem 4.9).
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

attribute [local irreducible] firstRoundedCandidate roundedCandidateSequence passageSequence
  firstSuccessfulCandidate

/-- A smaller tilt of the candidate overshoot weight is at most one plus a multiple of
the larger tilt. -/
theorem candidateOvershootWeight_le_tilt {d : ℕ} (Δ : ℝ≥0) (lam R L a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : 0 < b) (i : Fin d) (w : CoupledSample d) :
    candidateOvershootWeight Δ lam R L a i w ≤
      1 + ENNReal.ofReal (a / b) * candidateOvershootWeight Δ lam R L b i w := by
  by_cases hC : firstSuccessfulCandidate Δ lam R L w i ≠ ⊤
  · simp only [candidateOvershootWeight]
    rw [Set.indicator_of_mem (show w ∈ {w : CoupledSample d |
        firstSuccessfulCandidate Δ lam R L w i ≠ ⊤} from hC),
      Set.indicator_of_mem (show w ∈ {w : CoupledSample d |
        firstSuccessfulCandidate Δ lam R L w i ≠ ⊤} from hC),
      ← ENNReal.ofReal_mul (div_nonneg ha hb.le), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (mul_nonneg (div_nonneg ha hb.le) (Real.exp_pos _).le)]
    apply ENNReal.ofReal_le_ofReal
    set X := lam * (w.1 (firstSuccessfulCandidate Δ lam R L w i + Δ).toNNReal i - w.1 0 i - L / lam)
    have h := exp_mul_le_one_add_mul_exp (a / b) (b * X) (div_nonneg ha hb.le)
      ((div_le_one hb).mpr hab)
    have heq : a / b * (b * X) = a * X := by field_simp
    rw [heq] at h
    calc Real.exp (a * lam * (w.1 (firstSuccessfulCandidate Δ lam R L w i + Δ).toNNReal i -
          w.1 0 i - L / lam))
        = Real.exp (a * X) := by congr 1; ring
      _ ≤ 1 + a / b * Real.exp (b * X) := h
      _ = _ := by congr 3; ring
  · simp only [candidateOvershootWeight]
    rw [Set.indicator_of_notMem (show w ∉ {w : CoupledSample d |
      firstSuccessfulCandidate Δ lam R L w i ≠ ⊤} from hC)]
    exact zero_le

/-- Under the annealed split coupling, the running maximum at every finite trial start
exceeds the displacement there by at most `12R`. -/
theorem ae_trialStart_maximum_le {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) :
    ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ n : ℕ,
      trialStartSequence (Renewal.regenDelta lam) lam (l / lam) q.2 (Renewal.forceCoord hd) n ≠ ⊤ →
      coordinateMaximum q.2.1 (Renewal.forceCoord hd)
          (trialStartSequence (Renewal.regenDelta lam) lam (l / lam) q.2 (Renewal.forceCoord hd)
            n).toNNReal ≤
        q.2.1 (trialStartSequence (Renewal.regenDelta lam) lam (l / lam) q.2
          (Renewal.forceCoord hd) n).toNNReal (Renewal.forceCoord hd) -
          q.2.1 0 (Renewal.forceCoord hd) + 12 * (l / lam) := by
  let Δ := Renewal.regenDelta lam
  let R := l / lam
  let i := Renewal.forceCoord hd
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  have hR : 0 < R := div_pos hl h0
  have : IsProbabilityMeasure Q.measure := Q.probability
  rw [ae_all_iff]
  intro n
  have hS := (measurable_trialStartSequence Δ lam R i n).comp
    (measurable_snd : Measurable (Prod.snd : FieldPair d × CoupledSample d → _))
  have hpath : Measurable (fun q : FieldPair d × CoupledSample d => q.2.1) := measurable_snd.fst
  have hmax := (measurable_coordinateMaximum i).comp (hS.ennreal_toNNReal.prodMk hpath)
  have hx := measurable_path_eval.comp (hS.ennreal_toNNReal.prodMk hpath)
  have hx0 : Measurable (fun q : FieldPair d × CoupledSample d => q.2.1 0 i) :=
    (measurable_pi_apply i).comp ((continuous_eval_const (0 : ℝ≥0)).measurable.comp hpath)
  have hm : MeasurableSet {q : FieldPair d × CoupledSample d |
      trialStartSequence Δ lam R q.2 i n ≠ ⊤ →
        coordinateMaximum q.2.1 i (trialStartSequence Δ lam R q.2 i n).toNNReal ≤
          q.2.1 (trialStartSequence Δ lam R q.2 i n).toNNReal i - q.2.1 0 i + 12 * R} :=
    (hS (measurableSet_singleton ⊤)).compl.imp
      (measurableSet_le hmax ((((measurable_pi_apply i).comp hx).sub hx0).add_const _))
  apply Measure.ae_compProd_of_ae_ae hm
  filter_upwards [hK.1.1, hK.2.2.2.2.2.1.1] with ω hprob hsupp
  have : IsProbabilityMeasure (originCoupledLaw K ω) := hprob
  rw [Probability.probabilityPart_eq_of_isProbabilityMeasure (originCoupledLaw K) ω]
  filter_upwards [hsupp] with z hz
  exact fun hfin => trialStart_maximum_le Δ hΔ lam R h0 hR z i n hz hfin


/-- One step of the weighted trial recurrence: the next weighted trial start is at
most the current one times the failure factor and the candidate moment factor. -/
theorem trial_moment_step {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
    (a a₂ D₁ ρ q₁ : ℝ) (ha : 0 ≤ a) (ha₂ : 0 < a₂) (haa : a ≤ a₂)
    (h1st : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ (m : ℕ) (L : ℝ), 0 ≤ L →
      ∫⁻ w, failedRoundWeight (Renewal.regenDelta lam) lam (l / lam) L a₂ (Renewal.forceCoord hd) 0 w
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal D₁)
    (hcoin : ∀ᵐ q ∂annealedCoupledLaw Q.measure K, ∀ m : ℕ,
      ∫⁻ v, failedCoinWeight (Renewal.regenDelta lam) lam (l / lam) a₂ (Renewal.forceCoord hd) v
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ≤ ENNReal.ofReal ρ)
    (hfail : ∀ᵐ ω ∂Q.measure, ∀ y : Vec d,
      ∫⁻ γ, trialFailureWeight (Renewal.regenDelta lam) lam (l / lam) a (Renewal.forceCoord hd) γ
        ∂P (y, ω) ≤ ENNReal.ofReal q₁)
    (n : ℕ) :
    ∫⁻ q, trialStartWeight (Renewal.regenDelta lam) lam (l / lam) a (Renewal.forceCoord hd) (n + 1) q.2
        ∂annealedCoupledLaw Q.measure K ≤
      (1 + ENNReal.ofReal (a / a₂) * (ENNReal.ofReal (Real.exp (a₂ * lam * (11 * (l / lam)))) *
          ((1 - ENNReal.ofReal ρ)⁻¹ * ENNReal.ofReal D₁))) * ENNReal.ofReal q₁ *
        ∫⁻ q, trialStartWeight (Renewal.regenDelta lam) lam (l / lam) a (Renewal.forceCoord hd) n q.2
          ∂annealedCoupledLaw Q.measure K := by
  let Δ := Renewal.regenDelta lam
  have hΔ : 0 < Δ := EinsteinRelation.regenDelta_pos h0
  let R := l / lam
  have hR : 0 < R := div_pos hl h0
  let i := Renewal.forceCoord hd
  let μ := annealedCoupledLaw Q.measure K
  let B₀ : ℝ≥0∞ := ENNReal.ofReal (Real.exp (a₂ * lam * (11 * R))) *
    ((1 - ENNReal.ofReal ρ)⁻¹ * ENNReal.ofReal D₁)
  let S : CoupledSample d → ℝ≥0∞ := fun z => trialStartSequence Δ lam R z i n
  have hSm : Measurable S := measurable_trialStartSequence Δ lam R i n
  let F : CoupledSample d → ℝ≥0∞ := trialFailure Δ lam R i n
  have hFm : Measurable F :=
    (measurable_trialFailureTime Δ R i).comp (hSm.prodMk measurable_id)
  let W₀ : CoupledSample d → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (a * lam *
    (coordinateMaximum z.1 i (F z).toNNReal + R)))
  have hW₀m : Measurable W₀ :=
    ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (((measurable_coordinateMaximum i).comp (hFm.ennreal_toNNReal.prodMk measurable_fst)).add
        measurable_const)))
  let L₀ : CoupledSample d → ℝ := trialLevel Δ lam R i n
  have hL₀m : Measurable L₀ := by
    have hev : Measurable (fun z : CoupledSample d => z.1 (F z).toNNReal) :=
      measurable_path_eval.comp (hFm.ennreal_toNNReal.prodMk measurable_fst)
    exact measurable_const.mul ((((measurable_coordinateMaximum i).comp
      (hFm.ennreal_toNNReal.prodMk measurable_fst)).sub (((measurable_pi_apply i).comp hev).sub
        ((measurable_pi_apply i).comp ((continuous_eval_const 0).measurable.comp
          measurable_fst)))).add measurable_const)
  have hheight : ∀ z, trialFailureHeight Δ lam R a i n z =
      {z : CoupledSample d | F z ≠ ⊤}.indicator W₀ z := fun z => rfl
  -- the candidate moment
  have hFgrid : ∀ z, F z ≠ ⊤ → ∃ m : ℕ, F z = (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) :=
    fun z hz => trialFailureTime_mem_grid Δ R z i (S z) hz
  have hdecF : HistoryDecided Δ F (fun z => (W₀ z, L₀ z)) := by
    intro m z z' hag hz
    obtain ⟨hF', hHL⟩ := trialFailure_historyDecided Δ hΔ lam R a h0 hR i n m z z' hag hz
    simp only [Prod.mk.injEq] at hHL
    refine ⟨hF', ?_⟩
    have hzne : F z ≠ ⊤ := by rw [hz]; exact ENNReal.coe_ne_top
    have hz'ne : F z' ≠ ⊤ := by
      change trialFailure Δ lam R i n z' ≠ ⊤
      rw [hF']
      exact hzne
    have hW : W₀ z' = W₀ z := by
      have h := hHL.1
      rw [hheight, hheight, Set.indicator_of_mem (show z' ∈ {z : CoupledSample d | F z ≠ ⊤}
          from hz'ne), Set.indicator_of_mem (show z ∈ {z : CoupledSample d | F z ≠ ⊤}
          from hzne)] at h
      exact h
    simp only [Prod.mk.injEq]
    exact ⟨hW, hHL.2⟩
  have hcand := lintegral_candidateOvershoot_le hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
    a₂ D₁ ρ ha₂.le h1st hcoin F hFm hFgrid W₀ hW₀m L₀ hL₀m
    (fun z => trialLevel_nonneg Δ lam R h0 hR i n z) hdecF
  -- the failure factor
  let V : CoupledSample d → ℝ≥0∞ := fun z => ENNReal.ofReal (Real.exp (a * (lam *
    (z.1 (S z).toNNReal i - z.1 0 i))))
  have hVm : Measurable V := by
    have hev : Measurable (fun z : CoupledSample d => z.1 (S z).toNNReal) :=
      measurable_path_eval.comp (hSm.ennreal_toNNReal.prodMk measurable_fst)
    exact ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp (measurable_const.mul
      (measurable_const.mul (((measurable_pi_apply i).comp hev).sub ((measurable_pi_apply i).comp
        ((continuous_eval_const 0).measurable.comp measurable_fst))))))
  have hSgrid : ∀ z, S z ≠ ⊤ → ∃ m : ℕ, S z = (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) :=
    fun z hz => trialStartSequence_mem_grid Δ hΔ lam R z i n hz
  have hdecS : HistoryDecided Δ S (fun z => (V z,
      fun w : CoupledSample d => trialFailureWeight Δ lam R a i w.1)) := by
    intro m z z' hag hz
    obtain ⟨hS', hX⟩ := trialStart_historyDecided Δ hΔ lam R h0 hR i n m z z' hag hz
    refine ⟨hS', ?_⟩
    simp only [Prod.mk.injEq, and_true]
    have hXi := congrFun hX i
    simp only [Pi.sub_apply] at hXi
    simp only [V]
    rw [hXi]
  have hqmp : Measure.QuasiMeasurePreserving
      (Prod.fst : FieldPair d × CoupledSample d → FieldPair d) μ Q.measure := by
    refine ⟨measurable_fst, ?_⟩
    rw [EinsteinFull.Blueprint.c10_s3_annealed_environment_map Q K hK.1]
  have hinner : ∀ᵐ q ∂μ, ∀ m : ℕ, S q.2 = (((m : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) →
      ∫⁻ w, trialFailureWeight Δ lam R a i w.1 ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1) ≤
        ENNReal.ofReal q₁ := by
    have hmarg : ∀ᵐ q ∂μ, ∀ m : ℕ, (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)).map Prod.fst =
        P (q.2.1 ((m : ℝ≥0) * Δ), q.1) := by
      rw [ae_all_iff]
      exact fun m => EinsteinFull.Blueprint.c10_s3_grid_endpoint_path_marginal hd Q lam h0 h1 l δ
        P K hK m
    filter_upwards [hmarg, hqmp.ae hfail] with q hq hb m _
    have hmeas : Measurable (trialFailureWeight (d := d) Δ lam R a i) := by
      apply Measurable.indicator
      · apply ENNReal.measurable_ofReal.comp
        apply Real.measurable_exp.comp
        apply measurable_const.mul
        exact (measurable_const.max ((measurable_coordinateMaximum i).comp
          (((measurable_roundUp Δ).comp (measurable_first_downcrossing R i)).ennreal_toNNReal.prodMk
            measurable_id))).add measurable_const
      · exact (measurableSet_eq_fun (measurable_first_downcrossing R i) measurable_const).compl
    rw [← lintegral_map hmeas measurable_fst, hq m]
    exact hb _
  have hfailstep := lintegral_grid_stopping_le_of_decided hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK
    S hSm hSgrid V hVm (fun p => trialFailureWeight Δ lam R a i p.2.1)
    (by
      apply Measurable.comp _ measurable_snd.fst
      apply Measurable.indicator
      · apply ENNReal.measurable_ofReal.comp
        apply Real.measurable_exp.comp
        apply measurable_const.mul
        exact (measurable_const.max ((measurable_coordinateMaximum i).comp
          (((measurable_roundUp Δ).comp (measurable_first_downcrossing R i)).ennreal_toNNReal.prodMk
            measurable_id))).add measurable_const
      · exact (measurableSet_eq_fun (measurable_first_downcrossing R i) measurable_const).compl)
    hdecS (ENNReal.ofReal q₁) hinner
  have hgeom := ae_trialStart_maximum_le hd Q lam h0 h1 l δ hl P K hK
  -- assemble
  have hstart : ∀ z, trialStartWeight Δ lam R a i n z =
      {z : CoupledSample d | S z ≠ ⊤}.indicator V z := fun z => rfl
  calc ∫⁻ q, trialStartWeight Δ lam R a i (n + 1) q.2 ∂μ
      ≤ ∫⁻ q, ({z : CoupledSample d | F z ≠ ⊤}.indicator W₀ q.2 + ENNReal.ofReal (a / a₂) *
          {q : FieldPair d × CoupledSample d | F q.2 ≠ ⊤}.indicator (fun q => W₀ q.2 *
            candidateOvershootWeight Δ lam R (L₀ q.2) a₂ i (sampleTimeShift Δ q.2 (F q.2).toNNReal)) q)
          ∂μ := by
        apply lintegral_mono
        intro q
        beta_reduce
        rw [trialStartWeight_succ Δ lam R a h0 i n q.2]
        by_cases hq : F q.2 = ⊤
        · rw [Set.indicator_of_notMem (show q.2 ∉ {z : CoupledSample d |
            trialFailure Δ lam R i n z ≠ ⊤} from fun h => h hq)]
          exact zero_le
        · rw [Set.indicator_of_mem (show q.2 ∈ {z : CoupledSample d |
              trialFailure Δ lam R i n z ≠ ⊤} from hq), hheight q.2,
            Set.indicator_of_mem (show q.2 ∈ {z : CoupledSample d | F z ≠ ⊤} from hq),
            Set.indicator_of_mem (show q ∈ {q : FieldPair d × CoupledSample d | F q.2 ≠ ⊤} from hq)]
          calc W₀ q.2 * candidateOvershootWeight Δ lam R (trialLevel Δ lam R i n q.2) a i
                (sampleTimeShift Δ q.2 (trialFailure Δ lam R i n q.2).toNNReal)
              ≤ W₀ q.2 * (1 + ENNReal.ofReal (a / a₂) *
                  candidateOvershootWeight Δ lam R (L₀ q.2) a₂ i
                    (sampleTimeShift Δ q.2 (F q.2).toNNReal)) := by
                gcongr
                exact candidateOvershootWeight_le_tilt Δ lam R _ a a₂ ha haa ha₂ i _
            _ = _ := by ring
    _ = ∫⁻ q, {z : CoupledSample d | F z ≠ ⊤}.indicator W₀ q.2 ∂μ + ENNReal.ofReal (a / a₂) *
          ∫⁻ q, {q : FieldPair d × CoupledSample d | F q.2 ≠ ⊤}.indicator (fun q => W₀ q.2 *
            candidateOvershootWeight Δ lam R (L₀ q.2) a₂ i (sampleTimeShift Δ q.2 (F q.2).toNNReal)) q
          ∂μ := by
        have hmeasF : Measurable fun q : FieldPair d × CoupledSample d =>
            {z : CoupledSample d | F z ≠ ⊤}.indicator W₀ q.2 :=
          (hW₀m.indicator (measurableSet_eq_fun hFm measurable_const).compl).comp measurable_snd
        rw [lintegral_add_left hmeasF, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    _ ≤ ∫⁻ q, {z : CoupledSample d | F z ≠ ⊤}.indicator W₀ q.2 ∂μ + ENNReal.ofReal (a / a₂) *
          (B₀ * ∫⁻ q, {z : CoupledSample d | F z ≠ ⊤}.indicator W₀ q.2 ∂μ) := by
        gcongr
        have hI : ∫⁻ q, {q : FieldPair d × CoupledSample d | F q.2 ≠ ⊤}.indicator
            (fun q => W₀ q.2) q ∂μ = ∫⁻ q, {z : CoupledSample d | F z ≠ ⊤}.indicator W₀ q.2 ∂μ :=
          rfl
        rw [hI] at hcand
        refine hcand.trans (le_of_eq ?_)
        simp only [B₀]
        ring
    _ = (1 + ENNReal.ofReal (a / a₂) * B₀) *
          ∫⁻ q, trialFailureHeight Δ lam R a i n q.2 ∂μ := by
        simp only [hheight]
        ring
    _ ≤ (1 + ENNReal.ofReal (a / a₂) * B₀) * (ENNReal.ofReal q₁ *
          ∫⁻ q, trialStartWeight Δ lam R a i n q.2 ∂μ) := by
        gcongr
        calc ∫⁻ q, trialFailureHeight Δ lam R a i n q.2 ∂μ
            ≤ ∫⁻ q, {q : FieldPair d × CoupledSample d | S q.2 ≠ ⊤}.indicator (fun q => V q.2 *
                trialFailureWeight Δ lam R a i (sampleTimeShift Δ q.2 (S q.2).toNNReal).1) q ∂μ := by
              apply lintegral_mono_ae
              filter_upwards [hgeom] with q hq
              have h := trialFailureHeight_le Δ hΔ lam R a h0 ha i n q.2 (hq n)
              rw [hstart] at h
              by_cases hS : S q.2 = ⊤
              · simp only [Set.indicator, Set.mem_ofPred_eq, hS, ne_eq, not_true_eq_false,
                  ite_false, zero_mul] at h ⊢
                exact h
              · simp only [Set.indicator, Set.mem_ofPred_eq, hS, ne_eq, not_false_eq_true,
                  ite_true] at h ⊢
                exact h
          _ ≤ ENNReal.ofReal q₁ * ∫⁻ q, {q : FieldPair d × CoupledSample d | S q.2 ≠ ⊤}.indicator
                (fun q => V q.2) q ∂μ := hfailstep
          _ = ENNReal.ofReal q₁ * ∫⁻ q, trialStartWeight Δ lam R a i n q.2 ∂μ := rfl
    _ = _ := by ring

end EinsteinFull.Regeneration
