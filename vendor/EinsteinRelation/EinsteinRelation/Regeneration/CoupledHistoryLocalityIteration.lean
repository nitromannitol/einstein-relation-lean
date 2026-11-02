import EinsteinRelation.Regeneration.CoupledHistoryLocalityStep

/-!
# Iterating constrained one-interval locality

Source `paper/main.tex:377–381`. Positive-time endpoint absolute
continuity transfers the spatial-a.e. coupling facts to every actual
restart. The one-interval comparison then propagates to each complete
finite history.
-/

open MeasureTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- Spatial-a.e. supported first-interval identities and positive-time
endpoint densities determine every supported finite-history integral. -/
theorem integral_supported_histories_eq_of_first_interval_eq {d : ℕ}
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (V : Set (Vec d)) (hV : IsClosed V)
    (K K' : CoupledQuenchedLaws d) (p p' : Vec d × FieldPair d)
    [IsProbabilityMeasure (K p)] [IsProbabilityMeasure (K' p')]
    (hr : DeterministicRestartAt Δ K p) (hr' : DeterministicRestartAt Δ K' p')
    (hfirst : ∀ F : CoupledSample d → ℝ,
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F →
      BoundedRealTest F → (∀ z, F z ≠ 0 → z ∈ Probability.historyStays Δ 1 V) →
      (∫ z, F z ∂K p) = ∫ z, F z ∂K' p')
    (hspatial : ∀ᵐ x ∂(volume : Measure (Vec d)),
      IsProbabilityMeasure (K (x, p.2)) ∧ IsProbabilityMeasure (K' (x, p'.2)) ∧
        (x ∈ V → ∀ F : CoupledSample d → ℝ,
          @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F →
          BoundedRealTest F → (∀ z, F z ≠ 0 → z ∈ Probability.historyStays Δ 1 V) →
          (∫ z, F z ∂K (x, p.2)) = ∫ z, F z ∂K' (x, p'.2)))
    (hdensity : ∀ n : ℕ, 1 ≤ n →
      (K p).map (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ)) ≪
        (volume : Measure (Vec d)))
    (hdensity' : ∀ n : ℕ, 1 ≤ n →
      (K' p').map (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ)) ≪
        (volume : Measure (Vec d))) :
    ∀ n : ℕ, 1 ≤ n → ∀ F : CoupledSample d → ℝ,
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance F →
      BoundedRealTest F → (∀ z, F z ≠ 0 → z ∈ Probability.historyStays Δ n V) →
      (∫ z, F z ∂K p) = ∫ z, F z ∂K' p' := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => exact hfirst
  | succ n hn ih =>
    have heval : Measurable (fun z : CoupledSample d => z.1 ((n : ℝ≥0) * Δ)) :=
      (continuous_eval_const _).measurable.comp measurable_fst
    have hae : ∀ᵐ z ∂K p,
        IsProbabilityMeasure (K (z.1 ((n : ℝ≥0) * Δ), p.2)) ∧
          IsProbabilityMeasure (K' (z.1 ((n : ℝ≥0) * Δ), p'.2)) ∧
          (z.1 ((n : ℝ≥0) * Δ) ∈ V → ∀ F : CoupledSample d → ℝ,
            @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F →
            BoundedRealTest F → (∀ z, F z ≠ 0 → z ∈ Probability.historyStays Δ 1 V) →
            (∫ w, F w ∂K (z.1 ((n : ℝ≥0) * Δ), p.2)) =
              ∫ w, F w ∂K' (z.1 ((n : ℝ≥0) * Δ), p'.2)) :=
      ae_of_ae_map heval.aemeasurable ((hdensity n hn).ae_le hspatial)
    have hae' : ∀ᵐ z ∂K' p', IsProbabilityMeasure (K' (z.1 ((n : ℝ≥0) * Δ), p'.2)) :=
      (ae_of_ae_map heval.aemeasurable ((hdensity' n hn).ae_le hspatial)).mono fun _ h => h.2.1
    intro F hF hb hs
    apply integral_supported_history_succ_eq Δ hΔ n V hV K K' p p' hr hr'
      (hae.mono fun _ h => ⟨h.1, h.2.1⟩) hae' ih ?_ F hF hb hs
    filter_upwards [hae] with z hz
    intro hstay
    exact hz.2.2 (hstay _ le_rfl)


end EinsteinRelation.Regeneration
