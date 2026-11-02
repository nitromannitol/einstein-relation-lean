import EinsteinRelation.Probability.SupportedHistorySplit
import EinsteinRelation.Regeneration.DeterministicRestartJoint

/-!
# One induction step for constrained coupled-history locality

Source `paper/main.tex:377–381`. The last-interval restart, its supported
locality identity and the preceding-history identity imply the next
history identity. Exceptional starting fibres retain their probability
qualifiers; no pointwise Markov version is assumed.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

private theorem bounded_integral_probabilityPart {d : ℕ}
    (K : CoupledQuenchedLaws d) (p : Vec d × FieldPair d)
    (f : CoupledSample d → ℝ) (C : ℝ) (hC : 0 ≤ C) (hb : ∀ z, |f z| ≤ C) :
    |∫ z, f z ∂Probability.probabilityPart K p| ≤ C := by
  by_cases hp : K p Set.univ = 1
  · haveI : IsProbabilityMeasure (K p) := ⟨hp⟩
    rw [Probability.probabilityPart_eq_of_isProbabilityMeasure, ← Real.norm_eq_abs]
    simpa using norm_integral_le_of_norm_le_const
      (μ := K p) (f := f) (C := C)
      (Filter.Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb z)
  · simp only [Probability.probabilityPart_apply, if_neg hp, integral_zero_measure, abs_zero]
    exact hC

/-- The actual constrained finite-history comparison propagates across
one grid interval. The one-interval comparison is needed only at
almost every actual endpoint of the first law, while the preceding
history comparison applies to all bounded supported tests. -/
theorem integral_supported_history_succ_eq {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (n : ℕ) (V : Set (Vec d)) (hV : IsClosed V)
    (K K' : CoupledQuenchedLaws d) (p p' : Vec d × FieldPair d)
    [IsProbabilityMeasure (K p)] [IsProbabilityMeasure (K' p')]
    (hr : DeterministicRestartAt Δ K p) (hr' : DeterministicRestartAt Δ K' p')
    (hp : ∀ᵐ z ∂K p,
      IsProbabilityMeasure (K (z.1 ((n : ℝ≥0) * Δ), p.2)) ∧
        IsProbabilityMeasure (K' (z.1 ((n : ℝ≥0) * Δ), p'.2)))
    (hp' : ∀ᵐ z ∂K' p', IsProbabilityMeasure (K' (z.1 ((n : ℝ≥0) * Δ), p'.2)))
    (hprev : ∀ F : CoupledSample d → ℝ,
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance F →
      BoundedRealTest F → (∀ z, F z ≠ 0 → z ∈ Probability.historyStays Δ n V) →
      (∫ z, F z ∂K p) = ∫ z, F z ∂K' p')
    (hone : ∀ᵐ z ∂K p, z ∈ Probability.historyStays Δ n V →
      ∀ F : CoupledSample d → ℝ,
        @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F →
        BoundedRealTest F → (∀ w, F w ≠ 0 → w ∈ Probability.historyStays Δ 1 V) →
        (∫ w, F w ∂K (z.1 ((n : ℝ≥0) * Δ), p.2)) =
          ∫ w, F w ∂K' (z.1 ((n : ℝ≥0) * Δ), p'.2))
    (F : CoupledSample d → ℝ)
    (hF : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ (n + 1)) inferInstance F)
    (hb : BoundedRealTest F)
    (hsupport : ∀ z, F z ≠ 0 → z ∈ Probability.historyStays Δ (n + 1) V) :
    (∫ z, F z ∂K p) = ∫ z, F z ∂K' p' := by
  obtain ⟨G, hG, ⟨C, hbG⟩, hfactor, hsG⟩ :=
    Probability.exists_supported_splitHistory_factor Δ hΔ n V hV F hF hb hsupport
  have hC : 0 ≤ C := (abs_nonneg (G ((0, fun _ => false), (0, fun _ => false)))).trans (hbG _)
  let s := Probability.stoppedHistorySample (d := d) Δ n
  let t := Probability.stoppedHistorySample (d := d) Δ 1
  have hs : Measurable s := (Probability.measurable_stoppedHistorySample Δ n).mono
    (Probability.finiteHistorySigma_le Δ n) le_rfl
  have ht : Measurable t := (Probability.measurable_stoppedHistorySample Δ 1).mono
    (Probability.finiteHistorySigma_le Δ 1) le_rfl
  let J : CoupledSample d × CoupledSample d → ℝ := fun q => G (s q.1, t q.2)
  have hJ : Measurable J := hG.comp ((hs.comp measurable_fst).prodMk (ht.comp measurable_snd))
  have hbJ : BoundedRealTest J := ⟨C, fun _ => hbG _⟩
  let A : CoupledSample d → ℝ := fun z =>
    ∫ w, G (s z, t w) ∂Probability.probabilityPart K' (z.1 ((n : ℝ≥0) * Δ), p'.2)
  let L : Kernel (CoupledSample d) (CoupledSample d) := (Probability.probabilityPart K').comap
    (fun z : CoupledSample d => (z.1 ((n : ℝ≥0) * Δ), p'.2))
    (((continuous_eval_const _).measurable.comp measurable_fst).prodMk measurable_const)
  have hAm : Measurable A :=
    (hJ.stronglyMeasurable.integral_kernel_prod_right' (κ := L)).measurable
  have hAstop : ∀ z, A (s z) = A z := by
    intro z
    dsimp only [A]
    rw [show s (s z) = s z from Probability.stoppedHistorySample_idempotent Δ n z]
    rw [Probability.stoppedHistorySample_path Δ n z _ le_rfl]
  have hApast : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance A := by
    have h : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance
        (fun z => A (s z)) := hAm.comp (Probability.measurable_stoppedHistorySample Δ n)
    rwa [show (fun z => A (s z)) = A from funext hAstop] at h
  have hbA : BoundedRealTest A := ⟨C, fun z =>
    bounded_integral_probabilityPart K' _ _ C hC (fun _ => hbG _)⟩
  have hsAzero : ∀ z, z ∉ Probability.historyStays Δ n V → ∀ w, G (s z, t w) = 0 := by
    intro z hz w
    by_contra hn
    exact hz ((Probability.stoppedHistorySample_mem_historyStays_iff Δ n V z).mp (hsG _ hn).1)
  have hsA : ∀ z, A z ≠ 0 → z ∈ Probability.historyStays Δ n V := by
    intro z hn
    by_contra hz
    apply hn
    exact (integral_congr_ae (Filter.Eventually.of_forall (hsAzero z hz))).trans (integral_zero _ _)
  have hleft := integral_joint_of_deterministicRestartAt Δ K p hr n (hp.mono fun _ h => h.1) J hJ hbJ
  have hright := integral_joint_of_deterministicRestartAt Δ K' p' hr' n hp' J hJ hbJ
  have hfactor' : ∀ z : CoupledSample d,
      F z = J (Probability.stoppedHistorySample Δ n z,
        sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) := by
    intro z
    dsimp only [J]
    rw [show s (Probability.stoppedHistorySample Δ n z) = s z from
      Probability.stoppedHistorySample_idempotent Δ n z]
    exact hfactor z
  calc
    _ = ∫ z, J (Probability.stoppedHistorySample Δ n z,
        sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂K p :=
      integral_congr_ae (Filter.Eventually.of_forall hfactor')
    _ = ∫ z, ∫ w, J (Probability.stoppedHistorySample Δ n z, w)
        ∂K (z.1 ((n : ℝ≥0) * Δ), p.2) ∂K p := hleft
    _ = ∫ z, A z ∂K p := by
      apply integral_congr_ae
      filter_upwards [hp, hone] with z hz honez
      haveI := hz.2
      dsimp only [J, A]
      rw [show s (Probability.stoppedHistorySample Δ n z) = s z from
        Probability.stoppedHistorySample_idempotent Δ n z,
        Probability.probabilityPart_eq_of_isProbabilityMeasure]
      by_cases hzV : z ∈ Probability.historyStays Δ n V
      · apply honez hzV (fun w => G (s z, t w))
        · exact hG.comp (measurable_const.prodMk (Probability.measurable_stoppedHistorySample Δ 1))
        · exact ⟨C, fun _ => hbG _⟩
        · intro w hn
          exact (Probability.stoppedHistorySample_mem_historyStays_iff Δ 1 V w).mp (hsG _ hn).2
      · rw [integral_congr_ae (Filter.Eventually.of_forall (hsAzero z hzV)),
          integral_congr_ae (Filter.Eventually.of_forall (hsAzero z hzV))]
        simp only [integral_zero]
    _ = ∫ z, A z ∂K' p' := hprev A hApast hbA hsA
    _ = ∫ z, ∫ w, J (Probability.stoppedHistorySample Δ n z, w)
        ∂K' (z.1 ((n : ℝ≥0) * Δ), p'.2) ∂K' p' := by
      apply integral_congr_ae
      filter_upwards [hp'] with z hz
      haveI := hz
      dsimp only [A, J]
      rw [show s (Probability.stoppedHistorySample Δ n z) = s z from
        Probability.stoppedHistorySample_idempotent Δ n z,
        Probability.probabilityPart_eq_of_isProbabilityMeasure]
    _ = ∫ z, J (Probability.stoppedHistorySample Δ n z,
        sampleTimeShift Δ z ((n : ℝ≥0) * Δ)) ∂K' p' := hright.symm
    _ = _ := integral_congr_ae (Filter.Eventually.of_forall fun z => (hfactor' z).symm)


end EinsteinRelation.Regeneration
