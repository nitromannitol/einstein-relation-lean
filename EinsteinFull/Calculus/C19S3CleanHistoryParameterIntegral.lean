import EinsteinRelation.Regeneration.KilledFutureConditionalMean
import EinsteinRelation.Regeneration.DeterministicRestartJoint
import EinsteinRelation.Regeneration.DeterministicEndpointNullSets
import EinsteinRelation.Probability.FiniteHistoryStopping
import EinsteinFull.Frozen.RegenerationCoupling

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation Regeneration EinsteinRelation.External.GantertSection7Support

/-- The actual grid endpoint has a probability-law fibre, including at time zero. -/
private theorem c19_s3_grid_endpoint_probability {d : ℕ} (hd : 2 ≤ d)
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
private theorem c19_s3_history_parameter_restart {d : ℕ} (hd : 2 ≤ d)
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
  have hp := c19_s3_grid_endpoint_probability hd Q lam h0 h1 l δ P K hK m
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


/-- Extend deterministic restart to bounded tests with a history-measurable parameter. -/
theorem c19_s3_history_parameter_integral (history_factorization : ∀ {d : ℕ} (Δ : ℝ≥0) (m : ℕ) (A : Regeneration.CoupledSample d → ℝ), Measurable[Regeneration.finiteHistorySigma Δ m] A → ∃ a : Regeneration.CoupledSample d → ℝ, Measurable a ∧ ∀ z, A z = a (EinsteinRelation.Probability.stoppedHistorySample Δ m z)) {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ) (A : Regeneration.CoupledSample d → ℝ) (hA : Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] A) (H : Regeneration.CoupledSample d → ℝ) (hH : Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] H) (hbH : Regeneration.BoundedRealTest H) (F : ℝ × Regeneration.CoupledSample d → ℝ) (hF : Measurable F) (hbF : Regeneration.BoundedRealTest F) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; (∫ q, H q.2 * F (A q.2, Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂Regeneration.annealedCoupledLaw Q.measure K) = ∫ q, H q.2 * (∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) ∂Regeneration.annealedCoupledLaw Q.measure K := by
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
  have hr := c19_s3_history_parameter_restart hd Q lam h0 h1 l δ P K hK m G hG hbG
  dsimp only at hr ⊢
  simpa only [G, ← hAe, ← hbe, integral_const_mul] using hr


/-- The actual finite history determines both the parameter and the past test. -/
theorem c19_s3_actual_history_parameter_integral {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d) (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ) (A : Regeneration.CoupledSample d → ℝ) (hA : Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] A) (H : Regeneration.CoupledSample d → ℝ) (hH : Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] H) (hbH : Regeneration.BoundedRealTest H) (F : ℝ × Regeneration.CoupledSample d → ℝ) (hF : Measurable F) (hbF : Regeneration.BoundedRealTest F) : let Δ := Regeneration.Renewal.regenDelta lam; let R := l / lam; let i := Regeneration.Renewal.forceCoord hd; (∫ q, H q.2 * F (A q.2, Regeneration.sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)) ∂Regeneration.annealedCoupledLaw Q.measure K) = ∫ q, H q.2 * (∫ w, F (A q.2, w) ∂K (q.2.1 ((m : ℝ≥0) * Δ), q.1)) ∂Regeneration.annealedCoupledLaw Q.measure K := by
  refine c19_s3_history_parameter_integral ?_ hd Q lam h0 h1 l δ P K hK m A hA H hH hbH F hF hbF
  intro d Δ m A hA
  refine ⟨A, hA.mono (EinsteinRelation.Probability.finiteHistorySigma_le Δ m) le_rfl, ?_⟩
  intro z
  exact (EinsteinRelation.Probability.finiteHistory_test_stopped Δ m A hA z).symm

end EinsteinFull.Blueprint
