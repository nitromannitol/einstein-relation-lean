import EinsteinRelation.Regeneration.KilledFutureConditionalMean
import EinsteinRelation.Regeneration.DeterministicRestartJoint
import EinsteinFull.Calculus.C11ForcedSignedVelocity
import EinsteinFull.Calculus.U2GMPFinalEnvironment
import EinsteinFull.Calculus.U6RegularSignedPathRealization
import EinsteinFull.Blueprint.Foundation.Proofs.SbxS7ConditionalTrialExhaustion
import EinsteinFull.Blueprint.G1.Proofs.SbxS2KmDecomp

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration EinsteinRelation.External.GantertSection7Support

/-- The actual grid endpoint has a probability-law fibre, including at time zero. -/
private theorem c10_s3_grid_endpoint_probability {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ) :
    ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
      IsProbabilityMeasure (K (q.2.1 ((m : ℝ≥0) *
        Regeneration.Renewal.regenDelta lam), q.1)) := by
  by_cases hm : m = 0
  · subst m
    have hs := Regeneration.ae_origin_start_of_isGMPReducedKernel hd Q lam h0.le h1
      P K hK.1 hK.2.1 hK.2.2.1
    have hp : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
        IsProbabilityMeasure (K (0, q.1)) := by
      unfold Regeneration.annealedCoupledLaw
      apply Measure.ae_compProd_of_ae_ae
        (show MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
          IsProbabilityMeasure (K (0, q.1))} from
          by
            rw [show {q : FieldPair d × Regeneration.CoupledSample d |
              IsProbabilityMeasure (K (0, q.1))} =
              {q | K (0, q.1) Set.univ = 1} from by
                ext q
                exact ⟨fun h => h.measure_univ, fun h => ⟨h⟩⟩]
            exact ((K.measurable_coe MeasurableSet.univ)
              (measurableSet_singleton 1)).preimage (measurable_const.prodMk measurable_fst))
      filter_upwards [hK.1.1] with ω hω
      exact Filter.Eventually.of_forall fun _ => hω
    filter_upwards [hs, hp] with q hq hprob
    simpa only [Nat.cast_zero, zero_mul, hq] using hprob
  · have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
      Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
    have ht : 0 < (m : ℝ≥0) * Regeneration.Renewal.regenDelta lam :=
      mul_pos (by exact_mod_cast Nat.pos_of_ne_zero hm) hΔ
    exact Regeneration.ae_at_endpoint_of_product_ae hd Q lam h0.le h1 P K
      hK.1 hK.2.1 hK.2.2.1 _ ht _ hK.1.2


/-- Deterministic restart retains the entire observed coupled history. -/
private theorem c10_s3_history_parameter_restart {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ)
    (F : Regeneration.CoupledSample d × Regeneration.CoupledSample d → ℝ)
    (hF : Measurable F) (hbF : Regeneration.BoundedRealTest F) :
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    (∫ q, F (EinsteinRelation.Probability.stoppedHistorySample Δ m q.2,
      Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂μ) =
    ∫ q, ∫ w, F (EinsteinRelation.Probability.stoppedHistorySample Δ m q.2, w)
      ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1) ∂μ := by
  classical
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let X : Regeneration.CoupledSample d → Regeneration.CoupledSample d :=
    EinsteinRelation.Probability.stoppedHistorySample Δ m
  have hX : Measurable X := (EinsteinRelation.Probability.measurable_stoppedHistorySample Δ m).mono
    (EinsteinRelation.Probability.finiteHistorySigma_le Δ m) le_rfl
  let Y : FieldPair d × Regeneration.CoupledSample d → Regeneration.CoupledSample d :=
    fun q => Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
  have hY : Measurable Y := (Regeneration.measurable_sampleTimeShift Δ).comp
    (measurable_const.prodMk measurable_snd)
  let E : FieldPair d × Regeneration.CoupledSample d → Vec d × FieldPair d :=
    fun q => (q.2.1 ((m : ℝ≥0) * Δ), q.1)
  have hE : Measurable E := ((continuous_eval_const _).measurable.comp
    measurable_snd.fst).prodMk measurable_fst
  let L : Kernel (FieldPair d × Regeneration.CoupledSample d) (Regeneration.CoupledSample d) :=
    (EinsteinRelation.Probability.probabilityPart K).comap E hE
  let J : (FieldPair d × Regeneration.CoupledSample d) × Regeneration.CoupledSample d → ℝ :=
    fun q => F (X q.1.2, q.2)
  have hJ : Measurable J := hF.comp (((hX.comp measurable_fst.snd)).prodMk measurable_snd)
  let G : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q => ∫ w, J (q, w) ∂L q
  have hG : Measurable G := (hJ.stronglyMeasurable.integral_kernel_prod_right' (κ := L)).measurable
  obtain ⟨C, hC⟩ := hbF
  have hC0 : 0 ≤ C := (abs_nonneg (F (X (0, fun _ => false), (0, fun _ => false)))).trans (hC _)
  have hbG : Regeneration.BoundedRealTest G := by
    refine ⟨C, fun q => ?_⟩
    dsimp only [G, L, E, Kernel.comap_apply]
    by_cases hp : K (q.2.1 ((m : ℝ≥0) * Δ), q.1) Set.univ = 1
    · haveI : IsProbabilityMeasure (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) := ⟨hp⟩
      rw [EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure, ← Real.norm_eq_abs]
      simpa using norm_integral_le_of_norm_le_const
        (μ := K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) (f := fun w => J (q, w)) (C := C)
        (Filter.Eventually.of_forall fun w => by simpa only [Real.norm_eq_abs, J] using hC (X q.2, w))
    · simp only [EinsteinRelation.Probability.probabilityPart_apply, if_neg hp,
        integral_zero_measure, abs_zero]
      exact hC0
  let U : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q => F (X q.2, Y q)
  have hU : Measurable U := hF.comp ((hX.comp measurable_snd).prodMk hY)
  have hbU : Regeneration.BoundedRealTest U := ⟨C, fun q => hC _⟩
  have hp := c10_s3_grid_endpoint_probability hd Q lam h0 h1 l δ P K hK m
  have hpq := Regeneration.ae_quenched_of_annealed Q.measure K hK.1 hp
  have heq : (∫ q, G q ∂μ) = ∫ q, ∫ w, F (X q.2, w) ∂K (E q) ∂μ := by
    apply integral_congr_ae
    filter_upwards [hp] with q hq
    haveI := hq
    simp only [G, J, L, Kernel.comap_apply,
      EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]
  change (∫ q, U q ∂μ) = _
  rw [← heq, Regeneration.integral_annealedCoupledLaw Q.measure K hK.1 U hU hbU,
    Regeneration.integral_annealedCoupledLaw Q.measure K hK.1 G hG hbG]
  apply integral_congr_ae
  filter_upwards [hK.1.1, hK.2.2.2.2.1.1, hpq] with ω hω hr hprob
  haveI := hω
  have h := Regeneration.integral_joint_of_deterministicRestartAt Δ K (0, ω) hr m hprob F hF ⟨C, hC⟩
  refine h.trans (integral_congr_ae ?_)
  filter_upwards [hprob] with z hz
  haveI := hz
  simp only [G, J, L, E, X, Kernel.comap_apply,
    EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]


theorem c1_s3_history_parameter_integral (history_factorization : ∀ {d : ℕ} (Δ : ℝ≥0) (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), Measurable[Regeneration.finiteHistorySigma Δ m] A → ∃ a : Regeneration.CoupledSample d → ℝ, Measurable a ∧ ∀ z, A z = a (EinsteinRelation.Probability.stoppedHistorySample Δ m z)) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ) (A : Regeneration.CoupledSample d → ℝ) (hA : Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] A) (H : Regeneration.CoupledSample d → ℝ) (hH : Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] H) (hbH : Regeneration.BoundedRealTest H) (F : ℝ × Regeneration.CoupledSample d → ℝ) (hF : Measurable F) (hbF : Regeneration.BoundedRealTest F) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; (∫ q, H q.2 * F (A q.2, Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂Regeneration.annealedCoupledLaw Q.measure K) = ∫ q, H q.2 * (∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) ∂Regeneration.annealedCoupledLaw Q.measure K := by
  classical
  obtain ⟨a, ha, hAe⟩ := history_factorization _ _ A hA
  obtain ⟨h, hh, hHe⟩ := history_factorization _ _ H hH
  obtain ⟨C, hC⟩ := hbH
  obtain ⟨D, hD⟩ := hbF
  have hC0 : 0 ≤ C := (abs_nonneg (H (0, fun _ => false))).trans (hC _)
  have hD0 : 0 ≤ D := (abs_nonneg (F (0, (0, fun _ => false)))).trans (hD _)
  let b := fun z => max (-C) (min C (h z))
  have hb : Measurable b := measurable_const.max (measurable_const.min hh)
  have hb_bound : ∀ z, |b z| ≤ C := by
    intro z
    apply abs_le.mpr
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)
  have hbe : ∀ z, H z = b (EinsteinRelation.Probability.stoppedHistorySample
      (Regeneration.Renewal.regenDelta lam) m z) := by
    intro z
    have hz := abs_le.mp (hC z)
    rw [hHe z] at hz ⊢
    simp only [b, min_eq_right hz.2, max_eq_right hz.1]
  let G : Regeneration.CoupledSample d × Regeneration.CoupledSample d → ℝ :=
    fun p => b p.1 * F (a p.1, p.2)
  have hG : Measurable G := (hb.comp measurable_fst).mul
    (hF.comp ((ha.comp measurable_fst).prodMk measurable_snd))
  have hbG : Regeneration.BoundedRealTest G := by
    refine ⟨C * D, fun p => ?_⟩
    change |b p.1 * F (a p.1, p.2)| ≤ C * D
    rw [abs_mul]
    exact mul_le_mul (hb_bound _) (hD _) (abs_nonneg _) hC0
  have hr := c10_s3_history_parameter_restart hd Q lam h0 h1 l δ P K hK m G hG hbG
  dsimp only at hr ⊢
  simpa only [G, ← hAe, ← hbe, integral_const_mul] using hr

theorem c1_s3_actual_entries_of_escape_guard (hEscape : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t (Regeneration.Renewal.forceCoord hd)) Filter.atTop Filter.atTop) (hGuard : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; ε * (Regeneration.annealedCoupledLaw Q.measure K).real E ≤ (Regeneration.annealedCoupledLaw Q.measure K).real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N})) (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, ∀ m : ℕ, let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ); Regeneration.trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧ ∀ n : ℕ, Regeneration.trialFailureTime Δ R w i (Regeneration.trialStartSequence Δ lam R w i n) ≠ ⊤ → Regeneration.trialStartSequence Δ lam R w i (n + 1) ≠ ⊤ := by
  obtain ⟨ε, hε, hε1, hwin⟩ := hGuard htails hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  exact coupling_scope_ae_all_grid_trial_entries_of_escape_and_guard_estimates
    Q.measure K hK.1 _ hΔ δ hδ0 hδ1.le hK.2.2.2.1 lam (l / lam) h0
    (div_pos hl h0) (Regeneration.Renewal.forceCoord hd) ε hε hε1
    (hEscape htails hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD) hwin

theorem c1_s3_actual_history_parameter_integral {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ) (A : Regeneration.CoupledSample d → ℝ) (hA : Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] A) (H : Regeneration.CoupledSample d → ℝ) (hH : Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] H) (hbH : Regeneration.BoundedRealTest H) (F : ℝ × Regeneration.CoupledSample d → ℝ) (hF : Measurable F) (hbF : Regeneration.BoundedRealTest F) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; (∫ q, H q.2 * F (A q.2, Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂Regeneration.annealedCoupledLaw Q.measure K) = ∫ q, H q.2 * (∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) ∂Regeneration.annealedCoupledLaw Q.measure K := by
  refine c1_s3_history_parameter_integral ?_ hd Q lam h0 h1 l δ P K hK m A hA H hH hbH F hF hbF
  intro d Δ m A hA
  refine ⟨A, hA.mono (EinsteinRelation.Probability.finiteHistorySigma_le Δ m) le_rfl, ?_⟩
  intro z
  exact (EinsteinRelation.Probability.finiteHistory_test_stopped Δ m A hA z).symm

private theorem c1_s3_guard_of_stopped_tube (hTube : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let μ := Regeneration.annealedCoupledLaw Q.measure K; let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; let Tube := {q : FieldPair d × Regeneration.CoupledSample d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ, euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 ((couplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) - (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 (couplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}; ε * μ.real E ≤ μ.real (E ∩ Tube)) (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; ε * (Regeneration.annealedCoupledLaw Q.measure K).real E ≤ (Regeneration.annealedCoupledLaw Q.measure K).real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N}) := by
  obtain ⟨ε, hε, hε1, htube⟩ := hTube htails hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD
  refine ⟨ε, hε, hε1, ?_⟩
  intro m A hA N
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  let : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hΔ : 0 < Regeneration.Renewal.regenDelta lam :=
    Real.toNNReal_pos.mpr (inv_pos.mpr (sq_pos_of_pos h0))
  exact coupling_scope_guard_estimate_of_tube_estimate μ
    (Regeneration.Renewal.regenDelta lam) hΔ lam (l / lam) ε A m
    (Regeneration.Renewal.forceCoord hd) N (htube m A hA N)

theorem c1_s3_actual_entries_of_escape_tube (hEscape : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t (Regeneration.Renewal.forceCoord hd)) Filter.atTop Filter.atTop) (hTube : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let μ := Regeneration.annealedCoupledLaw Q.measure K; let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; let Tube := {q : FieldPair d × Regeneration.CoupledSample d | ∀ s ∈ Set.Icc (0 : ℝ≥0) Δ, euclideanNorm ((Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 ((couplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal + s) - (Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)).1 (couplingScopePassage Δ lam R A m i (2 * N) q.2).toNNReal) ≤ R / 2}; ε * μ.real E ≤ μ.real (E ∩ Tube)) (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, ∀ m : ℕ, let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ); Regeneration.trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧ ∀ n : ℕ, Regeneration.trialFailureTime Δ R w i (Regeneration.trialStartSequence Δ lam R w i n) ≠ ⊤ → Regeneration.trialStartSequence Δ lam R w i (n + 1) ≠ ⊤ := by
  exact c1_s3_actual_entries_of_escape_guard hEscape
    (c1_s3_guard_of_stopped_tube hTube) htails hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD

@[nolint unusedArguments]
private theorem c1_s3_escape_of_foundation_consumers
    (physical_mp_ae_unique : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
      (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) (PX PX' : QuenchedPathLaws d)
      (hX : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω)))
      (hX' : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))),
      ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω))
    (requested_s3_pathwise_foundation : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    (requested_s3_supplied_reduced_mp : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
      (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
      (P : QuenchedPathLaws d), IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P →
      ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (P (0, ω))) :
    ∀ (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d)
      {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam)
      (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
      (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d)
      (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
        Filter.Tendsto (fun t : ℝ≥0 => q.2.1 t (Regeneration.Renewal.forceCoord hd))
          Filter.atTop Filter.atTop := by
  intro _htails d hd Λ₀ r₀ Q lam h0 h1 l δ _hl _hsep _hδ0 _hδ1 P K hK _hD
  have hassoc : ∀ (d : ℕ) (hd : 2 ≤ d) (L R : ℝ) (Q : EnvironmentLaw d L R)
      (mu : ℝ) (hmu0 : 0 < mu) (hmu1 : mu ≤ 1)
      (P : ProbabilityTheory.Kernel (FieldPair d) (Path d)),
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω mu) 0 (P ω)) →
      IsGMPPhysicalOriginLaw hd Q.ellipticity_parameter Q mu hmu0.le hmu1 P := by
    intro d hd L R Q mu hmu0 hmu1 P hP
    obtain ⟨K, _, hsource, hKmp⟩ := u6_foundation_regular_signed_origin_law_and_mp
      hd Q.ellipticity_parameter Q mu hmu0.le hmu1
    exact physical_origin_law_of_source_mp physical_mp_ae_unique hd Q hmu0.le hmu1
      K P hsource hKmp hP
  have hY := requested_s3_supplied_reduced_mp hd Q lam h0.le h1 P hK.2.2.1
  obtain ⟨v, hv, hvpos⟩ := forced_reduced_signed_velocity_of_source_association
    hassoc requested_s3_pathwise_foundation d hd Λ₀ r₀ Q lam h0.ne' P hY
  have hpos : 0 < v (Regeneration.Renewal.forceCoord hd) :=
    (mul_pos_iff_of_pos_left h0).mp hvpos
  have hmeas : MeasurableSet {q : FieldPair d × Regeneration.CoupledSample d |
      HasPathVelocity q.2.1 v} :=
    measurableSet_joint_path_velocity.preimage
      ((measurable_fst.comp measurable_snd).prodMk measurable_const)
  have hvel : ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K,
      HasPathVelocity q.2.1 v := by
    apply Measure.ae_compProd_of_ae_ae hmeas
    filter_upwards [hK.1.1, hK.2.1.1, hv] with ω hprob hmap hvel
    let : IsProbabilityMeasure (Regeneration.originCoupledLaw K ω) := hprob
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure
      (Regeneration.originCoupledLaw K) ω]
    have hm : ∀ᵐ γ ∂(K (0, ω)).map Prod.fst, HasPathVelocity γ v := by
      rw [hmap]
      exact hvel
    exact ae_of_ae_map measurable_fst.aemeasurable hm
  filter_upwards [hvel] with q hq
  exact ConditionalTrialExhaustion.directional_escape_of_positive_velocity
    q.2.1 v (Regeneration.Renewal.forceCoord hd) hq hpos

theorem c1_s3_actual_entries_of_foundation_guard (physical_mp_ae_unique : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) (PX PX' : QuenchedPathLaws d) (hX : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) (hX' : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))), ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω)) (requested_s3_pathwise_foundation : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt) (requested_s3_supplied_reduced_mp : ∀ {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d), IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P → ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator (Regeneration.Renewal.forceCoord hd) ω lam) 0 (P (0, ω))) (hGuard : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; ε * (Regeneration.annealedCoupledLaw Q.measure K).real E ≤ (Regeneration.annealedCoupledLaw Q.measure K).real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N})) (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, ∀ m : ℕ, let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ); Regeneration.trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧ ∀ n : ℕ, Regeneration.trialFailureTime Δ R w i (Regeneration.trialStartSequence Δ lam R w i n) ≠ ⊤ → Regeneration.trialStartSequence Δ lam R w i (n + 1) ≠ ⊤ := by
  exact c1_s3_actual_entries_of_escape_guard
    (c1_s3_escape_of_foundation_consumers physical_mp_ae_unique
      requested_s3_pathwise_foundation requested_s3_supplied_reduced_mp)
    hGuard htails hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD

theorem c1_s3_entries_of_foundation_guard_reduced_mp_discharged (physical_mp_ae_unique : ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) (PX PX' : QuenchedPathLaws d) (hX : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) (hX' : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))), ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω)) (requested_s3_pathwise_foundation : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt) (hGuard : ∀ (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0), let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∃ ε : ℝ, 0 < ε ∧ ε ≤ 1 ∧ ∀ (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), @Measurable (Regeneration.CoupledSample d) ℝ (Regeneration.finiteHistorySigma Δ m) inferInstance A → ∀ N : ℕ, let E := couplingScopeEvenGuardFailure Δ lam R A m i Set.univ N ∩ {q | couplingScopePassage Δ lam R A m i (2 * N) q.2 ≠ ⊤}; ε * (Regeneration.annealedCoupledLaw Q.measure K).real E ≤ (Regeneration.annealedCoupledLaw Q.measure K).real (E ∩ {q | q.2 ∈ couplingScopeEvenGuard Δ lam R A m i N})) (htails : node_app_u3A_regen_u2D_tailsStmt) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (hD : Regeneration.annealedCoupledLaw Q.measure K (regenerationNoReturn hd (l / lam)) ≠ 0) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; ∀ᵐ q ∂Regeneration.annealedCoupledLaw Q.measure K, ∀ m : ℕ, let w := Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ); Regeneration.trialStartSequence Δ lam R w i 0 ≠ ⊤ ∧ ∀ n : ℕ, Regeneration.trialFailureTime Δ R w i (Regeneration.trialStartSequence Δ lam R w i n) ≠ ⊤ → Regeneration.trialStartSequence Δ lam R w i (n + 1) ≠ ⊤ := by
  exact c1_s3_actual_entries_of_foundation_guard physical_mp_ae_unique
    requested_s3_pathwise_foundation EinsteinFull.u2_arbitrary_supplied_reduced_kernel_MP
    hGuard htails hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK hD

theorem c1_s3_actual_history_parameter_integral_checked {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ) (A : Regeneration.CoupledSample d → ℝ) (hA : Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] A) (H : Regeneration.CoupledSample d → ℝ) (hH : Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] H) (hbH : Regeneration.BoundedRealTest H) (F : ℝ × Regeneration.CoupledSample d → ℝ) (hF : Measurable F) (hbF : Regeneration.BoundedRealTest F) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; (∫ q, H q.2 * F (A q.2, Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂Regeneration.annealedCoupledLaw Q.measure K) = ∫ q, H q.2 * (∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) ∂Regeneration.annealedCoupledLaw Q.measure K := by
  exact c1_s3_actual_history_parameter_integral hd Q lam h0 h1 l δ P K hK m A hA H hH hbH F hF hbF

/-- Conditional expectations of bounded history-level tests are integrable. -/
theorem c1_s3_history_level_conditional_integrable {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ)
    (A : Regeneration.CoupledSample d → ℝ) (hA : Measurable A)
    (F : ℝ × Regeneration.CoupledSample d → ℝ) (hF : Measurable F)
    (hbF : Regeneration.BoundedRealTest F) :
    let Δ := Regeneration.Renewal.regenDelta lam
    Integrable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      ∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1))
      (Regeneration.annealedCoupledLaw Q.measure K) := by
  dsimp only
  let Δ := Regeneration.Renewal.regenDelta lam
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  haveI : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let E : FieldPair d × Regeneration.CoupledSample d → Vec d × FieldPair d :=
    fun q => (q.2.1 ((m : ℝ≥0) * Δ), q.1)
  have hE : Measurable E := ((continuous_eval_const _).measurable.comp
    measurable_snd.fst).prodMk measurable_fst
  let L : Kernel (FieldPair d × Regeneration.CoupledSample d) (Regeneration.CoupledSample d) :=
    (EinsteinRelation.Probability.probabilityPart K).comap E hE
  let J : (FieldPair d × Regeneration.CoupledSample d) × Regeneration.CoupledSample d → ℝ :=
    fun q => F (A q.1.2, q.2)
  have hJ : Measurable J := hF.comp (((hA.comp measurable_fst.snd)).prodMk measurable_snd)
  let G : FieldPair d × Regeneration.CoupledSample d → ℝ := fun q => ∫ w, J (q, w) ∂L q
  have hG : Measurable G := (hJ.stronglyMeasurable.integral_kernel_prod_right' (κ := L)).measurable
  obtain ⟨C, hC⟩ := hbF
  have hC0 : 0 ≤ C := (abs_nonneg (F (0, (0, fun _ => false)))).trans (hC _)
  have hbG : ∀ q, ‖G q‖ ≤ C := by
    intro q
    dsimp only [G, L, E, Kernel.comap_apply]
    by_cases hp : K (q.2.1 ((m : ℝ≥0) * Δ), q.1) Set.univ = 1
    · haveI : IsProbabilityMeasure (K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) := ⟨hp⟩
      rw [EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]
      simpa using norm_integral_le_of_norm_le_const
        (μ := K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) (f := fun w => J (q, w)) (C := C)
        (Filter.Eventually.of_forall fun w => by
          simpa only [Real.norm_eq_abs, J] using hC (A q.2, w))
    · simp only [EinsteinRelation.Probability.probabilityPart_apply, if_neg hp,
        integral_zero_measure, norm_zero]
      exact hC0
  have hi : Integrable G μ := Integrable.of_bound hG.aestronglyMeasurable C
    (Filter.Eventually.of_forall hbG)
  apply hi.congr
  filter_upwards [c10_s3_grid_endpoint_probability hd Q lam h0 h1 l δ P K hK m] with q hq
  haveI := hq
  simp only [G, J, L, E, Kernel.comap_apply, Δ,
    EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]


/-- The burn indicator times the actual endpoint killed-future average is integrable. -/
@[nolint unusedArguments]
theorem c1_s3_actual_burn_endpoint_product_integrable {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam)
    (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l)
    (hδ0 : 0 < δ) (hδ1 : δ < 1) (P : QuenchedPathLaws d)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m J N k : ℕ) :
    Integrable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      (couplingScopeTrialBurnPrebridge (Regeneration.Renewal.regenDelta lam) lam (l / lam)
        m (Regeneration.Renewal.forceCoord hd) J N k).indicator (fun _ => (1 : ℝ)) q.2 *
      Regeneration.endpointAverage (Regeneration.Renewal.forceCoord hd) (l / lam)
        (q.2.1 (((m + k : ℕ) : ℝ≥0) * Regeneration.Renewal.regenDelta lam))
        (fun y => ∫ w, Regeneration.killedFutureTest (l / lam)
          (Regeneration.Renewal.forceCoord hd) (fun _ => (1 : ℝ)) ((y, q.1), w)
            ∂K (y, q.1))) (Regeneration.annealedCoupledLaw Q.measure K) := by
  classical
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  let Δ := Regeneration.Renewal.regenDelta lam
  let A := couplingScopeTrialBurnPrebridge Δ lam R m i J N k
  let μ := Regeneration.annealedCoupledLaw Q.measure K
  obtain ⟨C, _, B, hB, hbB, _, hBp⟩ :=
    Regeneration.exists_globally_bounded_measurable_killed_future_version
      Q.measure K hK.1 R i (fun _ => (1 : ℝ)) measurable_const ⟨1, by simp⟩
  let X : FieldPair d × Regeneration.CoupledSample d → Vec d :=
    fun q => q.2.1 (((m + k : ℕ) : ℝ≥0) * Δ)
  let B' : (FieldPair d × Regeneration.CoupledSample d) × Vec d → ℝ :=
    fun p => B (p.2, p.1.1)
  have hX : Measurable X := (continuous_eval_const _).measurable.comp measurable_snd.fst
  have hB' : Measurable B' := hB.comp (measurable_snd.prodMk measurable_fst.fst)
  have hm := Regeneration.measurable_endpointAverage i R X hX B' hB'
  obtain ⟨D, hD⟩ := Regeneration.boundedRealTest_endpointAverage i R (div_pos hl h0)
    X B' ⟨C, fun p => hbB (p.2, p.1.1)⟩
  have hA : MeasurableSet A := coupling_scope_measurableSet_trial_burn_prebridge Δ lam R m i J N k
  have hI : Measurable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      A.indicator (fun _ => (1 : ℝ)) q.2) :=
    (measurable_const.indicator hA).comp measurable_snd
  haveI : IsProbabilityMeasure μ :=
    Regeneration.annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  have hi : Integrable (fun q : FieldPair d × Regeneration.CoupledSample d =>
      A.indicator (fun _ => (1 : ℝ)) q.2 *
        Regeneration.endpointAverage i R (X q) (fun y => B' (q, y))) μ := by
    apply Integrable.of_bound (hI.mul hm).aestronglyMeasurable (max D 0)
    filter_upwards [] with q
    by_cases hq : q.2 ∈ A
    · simpa [hq, Real.norm_eq_abs] using (hD q).trans (le_max_left D 0)
    · simp [hq, le_max_right D 0]
  have heq : ∀ᵐ ω ∂Q.measure, ∀ᵐ y ∂(volume : Measure (Vec d)),
      B (y, ω) = ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ))
        ((y, ω), z) ∂K (y, ω) := by
    have hh := Measure.ae_ae_of_ae_prod
      (Measure.measurePreserving_swap.quasiMeasurePreserving.ae_eq_comp hBp)
    filter_upwards [hh] with ω hω
    filter_upwards [hω] with y hy
    simpa only [Function.comp_apply, Prod.swap, Regeneration.killedFutureTest,
      Regeneration.spatialFutureRecord] using hy
  have hq : ∀ᵐ q ∂μ, ∀ᵐ y ∂(volume : Measure (Vec d)),
      B (y, q.1) = ∫ z, Regeneration.killedFutureTest R i (fun _ => (1 : ℝ))
        ((y, q.1), z) ∂K (y, q.1) := by
    have hm := sbxS2_map_fst_annealed Q K hK.1
    exact (show MeasurePreserving Prod.fst μ Q.measure from ⟨measurable_fst, hm⟩).quasiMeasurePreserving.ae heq
  apply hi.congr
  filter_upwards [hq] with q hq
  dsimp only [A, X, B', R, i, Δ]
  congr 1
  unfold Regeneration.endpointAverage
  congr 1
  exact integral_congr_ae (ae_restrict_of_ae hq)

end EinsteinFull.Blueprint
