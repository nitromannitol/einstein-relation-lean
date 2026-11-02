import EinsteinRelation.Regeneration.DeterministicRestartJoint
import EinsteinRelation.Probability.FiniteHistoryStopping
import EinsteinRelation.Probability.FiniteHistoryFiltration

/-!
# Restart followed by the uniform successful endpoint

Source `paper/main.tex:383–397`. The future test may depend jointly on the
physical endpoint and the restarted sample. Deterministic restart first
integrates out the future; the uniform-endpoint identity then integrates
the endpoint over the actual ball used by the coupling.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- The quenched restart and uniform-endpoint part of `regen.slice-factor`
(`paper/main.tex:383–397`). The version `B` need agree with the future kernel
integral only at almost every actual deterministic-time endpoint. -/
theorem integral_future_eq_uniformEndpointAverage {d : ℕ}
    (Δ : ℝ≥0) (δ R : ℝ) (i : Fin d) (K : CoupledQuenchedLaws d)
    (xω : Vec d × FieldPair d) [IsProbabilityMeasure (K xω)]
    (hRestart : DeterministicRestartAt Δ K xω)
    (hUniform : UniformSuccessfulEndpointAt Δ δ R i K xω)
    (m : ℕ) (hprob : ∀ᵐ z ∂K xω,
      IsProbabilityMeasure (K (z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), xω.2)))
    (H : CoupledSample d → ℝ)
    (hH : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H)
    (hbH : BoundedRealTest H)
    (Ψ : Vec d × CoupledSample d → ℝ) (hΨ : Measurable Ψ) (hbΨ : BoundedRealTest Ψ)
    (B : Vec d → ℝ) (hB : Measurable B) (hbB : BoundedRealTest B)
    (hBeq : ∀ᵐ z ∂K xω,
      B (z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ)) =
        ∫ w, Ψ (z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), w)
          ∂K (z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ), xω.2)) :
    (∫ z, H z * (if z.2 m = true then (1 : ℝ) else 0) *
      Ψ (z.1 (((m + 1 : ℕ) : ℝ≥0) * Δ),
        sampleTimeShift Δ z (((m + 1 : ℕ) : ℝ≥0) * Δ)) ∂K xω) =
      δ * ∫ z, H z * endpointAverage i R (z.1 ((m : ℝ≥0) * Δ)) B ∂K xω := by
  classical
  let t : ℝ≥0 := ((m + 1 : ℕ) : ℝ≥0) * Δ
  let F : CoupledSample d × CoupledSample d → ℝ := fun q =>
    H q.1 * (if q.1.2 m = true then 1 else 0) * Ψ (q.1.1 t, q.2)
  have hHfull := hH.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
  have hF : Measurable F := by
    exact ((hHfull.comp measurable_fst).mul
      (Measurable.ite (((measurable_pi_apply m).comp measurable_fst.snd)
        (measurableSet_singleton true)) measurable_const measurable_const)).mul
      (hΨ.comp ((((continuous_eval_const t).measurable.comp measurable_fst.fst)).prodMk
        measurable_snd))
  have hbF : BoundedRealTest F := by
    obtain ⟨CH, hCH⟩ := hbH
    obtain ⟨CP, hCP⟩ := hbΨ
    refine ⟨max CH 0 * max CP 0, fun q => ?_⟩
    dsimp [F]
    by_cases hq : q.1.2 m = true
    · simp only [hq, ↓reduceIte, mul_one, abs_mul]
      exact mul_le_mul (le_trans (hCH _) (le_max_left _ _))
        (le_trans (hCP _) (le_max_left _ _)) (abs_nonneg _) (le_max_right _ _)
    · simpa [hq] using
        (mul_nonneg (le_max_right CH (0 : ℝ)) (le_max_right CP (0 : ℝ)))
  have hHstop : ∀ z, H (Probability.stoppedHistorySample Δ (m + 1) z) = H z :=
    Probability.finiteHistory_test_stopped Δ (m + 1) H
      (hH.mono (finiteHistorySigma_mono Δ (Nat.le_succ m)) le_rfl)
  have hFstop : ∀ z w,
      F (Probability.stoppedHistorySample Δ (m + 1) z, w) =
        H z * (if z.2 m = true then 1 else 0) * Ψ (z.1 t, w) := by
    intro z w
    dsimp only [F]
    rw [hHstop, Probability.stoppedHistorySample_bit Δ (m + 1) z m (Nat.lt_succ_self m),
      Probability.stoppedHistorySample_path Δ (m + 1) z t le_rfl]
  have heq := integral_joint_of_deterministicRestartAt Δ K xω hRestart (m + 1)
    hprob F hF hbF
  simp_rw [hFstop, integral_const_mul] at heq
  refine heq.trans ((integral_congr_ae ?_).trans (hUniform m H B hH hbH hB hbB))
  filter_upwards [hBeq] with z hz
  rw [hz]


end EinsteinRelation.Regeneration
