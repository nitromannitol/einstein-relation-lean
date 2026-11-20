import EinsteinFull.Calculus.C10S3StoppedTubeProducer
import EinsteinRelation.Regeneration.DeterministicRestartJoint

/-!
# Annealed restarts of the split coupling against nonnegative weights

The deterministic restart of the split coupling identifies the joint law of the
stopped history at a grid time and the shifted coupled sample. Hence every
nonnegative measurable functional of the pair restarts, and so does every
functional at a grid-valued time whose slices are decided by the stopped history.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- Restart of the annealed coupled law at a deterministic grid time, for every
nonnegative measurable functional of the stopped history and the shifted sample. -/
theorem lintegral_history_restart {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ)
    (h0 : 0 < lam) (h1 : lam ≤ 1) (l δ : ℝ) (hl : 0 < l)
    (hsep : r₀ < 2 * l) (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h0.le h1 P K) (m : ℕ)
    (G : CoupledSample d × CoupledSample d → ℝ≥0∞) (hG : Measurable G) :
    (∫⁻ q, G (EinsteinRelation.Probability.stoppedHistorySample (Renewal.regenDelta lam) m q.2,
        sampleTimeShift (Renewal.regenDelta lam) q.2 ((m : ℝ≥0) * Renewal.regenDelta lam))
        ∂annealedCoupledLaw Q.measure K) =
      ∫⁻ q, ∫⁻ w, G (EinsteinRelation.Probability.stoppedHistorySample
          (Renewal.regenDelta lam) m q.2, w)
        ∂K (q.2.1 ((m : ℝ≥0) * Renewal.regenDelta lam), q.1) ∂annealedCoupledLaw Q.measure K := by
  let Δ := Renewal.regenDelta lam
  let μ := annealedCoupledLaw Q.measure K
  have : IsProbabilityMeasure Q.measure := Q.probability
  have : IsProbabilityMeasure μ := annealedCoupledLaw_isProbabilityMeasure Q.measure K hK.1
  let X : FieldPair d × CoupledSample d → CoupledSample d :=
    fun q => EinsteinRelation.Probability.stoppedHistorySample Δ m q.2
  have hX : Measurable X :=
    ((EinsteinRelation.Probability.measurable_stoppedHistorySample Δ m).mono
      (EinsteinRelation.Probability.finiteHistorySigma_le Δ m) le_rfl).comp measurable_snd
  let Y : FieldPair d × CoupledSample d → CoupledSample d :=
    fun q => sampleTimeShift Δ q.2 ((m : ℝ≥0) * Δ)
  have hY : Measurable Y := (measurable_sampleTimeShift Δ).comp
    (measurable_const.prodMk measurable_snd)
  let E : FieldPair d × CoupledSample d → Vec d × FieldPair d :=
    fun q => (q.2.1 ((m : ℝ≥0) * Δ), q.1)
  have hE : Measurable E := ((continuous_eval_const _).measurable.comp
    measurable_snd.fst).prodMk measurable_fst
  let L : Kernel (FieldPair d × CoupledSample d) (CoupledSample d) :=
    (EinsteinRelation.Probability.probabilityPart K).comap E hE
  have hp := EinsteinFull.Blueprint.c10_s3_grid_endpoint_probability hd Q lam h0 h1 l δ P K hK m
  have hLK : ∀ᵐ q ∂μ, L q = K (E q) := by
    filter_upwards [hp] with q hq
    have := hq
    simp only [L, Kernel.comap_apply,
      EinsteinRelation.Probability.probabilityPart_eq_of_isProbabilityMeasure]
  have hpair : μ.map (fun q => (X q, Y q)) = (μ.compProd L).map (fun q => (X q.1, q.2)) := by
    apply map_pair_eq_restart_of_product_tests μ X Y hX hY L
    intro H Φ hH hbH hΦ hbΦ
    have hr := EinsteinFull.Blueprint.c10_s3_history_parameter_restart hd Q lam h0 h1 l δ hl hsep hδ0 hδ1 P K hK m
      (fun p => H p.1 * Φ p.2) ((hH.comp measurable_fst).mul (hΦ.comp measurable_snd))
      (by
        obtain ⟨A, hA⟩ := hbH
        obtain ⟨B, hB⟩ := hbΦ
        refine ⟨A * B, fun p => ?_⟩
        rw [abs_mul]
        exact mul_le_mul (hA _) (hB _) (abs_nonneg _) ((abs_nonneg _).trans (hA p.1)))
    simp only at hr
    refine hr.trans (integral_congr_ae ?_)
    filter_upwards [hLK] with q hq
    simp only [X, hq, integral_const_mul]
    rfl
  calc (∫⁻ q, G (X q, Y q) ∂μ)
      = ∫⁻ p, G p ∂(μ.map (fun q => (X q, Y q))) :=
        (lintegral_map hG (hX.prodMk hY)).symm
    _ = ∫⁻ p, G p ∂((μ.compProd L).map (fun q => (X q.1, q.2))) := by rw [hpair]
    _ = ∫⁻ q, G (X q.1, q.2) ∂(μ.compProd L) :=
        lintegral_map hG ((hX.comp measurable_fst).prodMk measurable_snd)
    _ = ∫⁻ q, ∫⁻ w, G (X q, w) ∂L q ∂μ :=
        Measure.lintegral_compProd (hG.comp ((hX.comp measurable_fst).prodMk measurable_snd))
    _ = ∫⁻ q, ∫⁻ w, G (X q, w) ∂K (E q) ∂μ := by
        apply lintegral_congr_ae
        filter_upwards [hLK] with q hq
        rw [hq]

end EinsteinFull.Regeneration
