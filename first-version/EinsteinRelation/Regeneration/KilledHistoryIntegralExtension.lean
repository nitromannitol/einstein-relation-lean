import EinsteinRelation.Regeneration.CoupledHistoryLocalityIteration
import EinsteinRelation.Regeneration.NoBacktrackingPrefix
import EinsteinRelation.Probability.FiniteHistoryLpDensity
import EinsteinRelation.Probability.FiniteHistoryExhaustion
import EinsteinRelation.Probability.IncreasingSigmaMeasureExt
import EinsteinRelation.Regeneration.FiniteBarrierLimit

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinRelation.Regeneration

/-- Source `paper/main.tex:387`: monotone-class and bounded-convergence extension from constrained finite histories to the entire killed future. -/
theorem integral_killed_eq_of_supported_history_integrals {d : ℕ}
    (μ ν : Measure (CoupledSample d)) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (i : Fin d)
    (hs : ∀ᵐ z ∂μ, z.1 0 = 0) (hs' : ∀ᵐ z ∂ν, z.1 0 = 0)
    (hfinite : ∀ (n : ℕ), 1 ≤ n → ∀ F : CoupledSample d → ℝ,
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance F →
      BoundedRealTest F →
      (∀ z, F z ≠ 0 → ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R ≤ z.1 t i) →
      (∫ z, F z ∂μ) = ∫ z, F z ∂ν)
    (F : CoupledSample d → ℝ) (hF : Measurable F) (hb : BoundedRealTest F) :
    (∫ z, (if NoBacktracking R z.1 i then F z else 0) ∂μ) =
      ∫ z, (if NoBacktracking R z.1 i then F z else 0) ∂ν := by
  have hprefix : ∀ (m n : ℕ), m ≤ n → 1 ≤ n → ∀ H : CoupledSample d → ℝ,
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H →
      BoundedRealTest H →
      (∫ z, (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
        then H z else 0) ∂μ) =
      ∫ z, (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
        then H z else 0) ∂ν := by
    intro m n hmn hn H hH hbH
    let G : CoupledSample d → ℝ := fun z =>
      if z.1 0 = 0 ∧ ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
        then H z else 0
    have hzero : @Measurable (CoupledSample d) (Vec d)
        (finiteHistorySigma Δ n) inferInstance (fun z => z.1 0) := by
      have h := ((continuous_eval_const (0 : ℝ≥0)).measurable.comp measurable_fst).comp
        (Probability.measurable_stoppedHistorySample (d := d) Δ n)
      change @Measurable (CoupledSample d) (Vec d) (finiteHistorySigma Δ n) inferInstance
        (fun z => (Probability.stoppedHistorySample Δ n z).1 0) at h
      simpa only [Probability.stoppedHistorySample_path Δ n _ 0 (zero_le _)] using h
    have hG : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance G :=
      Measurable.ite ((measurableSet_eq_fun hzero measurable_const).inter
        (measurableSet_noBacktracking_prefix Δ n R i))
        (hH.mono (finiteHistorySigma_mono Δ hmn) le_rfl) measurable_const
    obtain ⟨C, hbC⟩ := hbH
    have hbG : BoundedRealTest G := by
      refine ⟨max C 0, fun z => ?_⟩
      dsimp only [G]
      split_ifs
      · exact (hbC z).trans (le_max_left _ _)
      · simpa only [abs_zero] using (le_max_right C 0)
    have hsG : ∀ z, G z ≠ 0 → ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R ≤ z.1 t i := by
      intro z hz t ht
      have hzcond : z.1 0 = 0 ∧ ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ →
          -R < z.1 t i - z.1 0 i := by
        by_contra h
        exact hz (if_neg h)
      have h := hzcond.2 t ht
      rw [hzcond.1] at h
      simpa only [Pi.zero_apply, sub_zero] using h.le
    have hcomp := hfinite n hn G hG hbG hsG
    have hchange : ∀ (ρ : Measure (CoupledSample d)), (∀ᵐ z ∂ρ, z.1 0 = 0) →
        (∫ z, G z ∂ρ) = ∫ z,
          (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i
            then H z else 0) ∂ρ := by
      intro ρ hρ
      apply integral_congr_ae
      filter_upwards [hρ] with z hz
      simp only [G, hz, true_and]
    rwa [hchange μ hs, hchange ν hs'] at hcomp
  have hkilled : ∀ (m : ℕ) (H : CoupledSample d → ℝ),
      @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ m) inferInstance H →
      BoundedRealTest H →
      (∫ z, (if NoBacktracking R z.1 i then H z else 0) ∂μ) =
        ∫ z, (if NoBacktracking R z.1 i then H z else 0) ∂ν := by
    intro m H hH hbH
    have hHm := hH.mono (Probability.finiteHistorySigma_le Δ m) le_rfl
    have hμ := tendsto_integral_finite_barrier μ Δ hΔ R i H hHm hbH
    have hν := tendsto_integral_finite_barrier ν Δ hΔ R i H hHm hbH
    have heq : (fun n : ℕ => ∫ z,
        (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i then H z else 0) ∂μ)
        =ᶠ[Filter.atTop] (fun n : ℕ => ∫ z,
        (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i then H z else 0) ∂ν) := by
      filter_upwards [Filter.eventually_ge_atTop (max m 1)] with n hn
      exact hprefix m n ((le_max_left _ _).trans hn) ((le_max_right _ _).trans hn) H hH hbH
    exact tendsto_nhds_unique (hμ.congr' heq) hν
  let D : Set (CoupledSample d) := {z | NoBacktracking R z.1 i}
  have hD : MeasurableSet D := (measurableSet_NoBacktracking R i).preimage measurable_fst
  have heq : μ.restrict D = ν.restrict D := by
    apply Probability.measure_eq_of_increasing_sigma (μ.restrict D) (ν.restrict D)
      (finiteHistorySigma Δ) (fun a b h => finiteHistorySigma_mono Δ h) (iSup_finiteHistorySigma_eq Δ hΔ)
    intro n s hs
    have hs' := Probability.finiteHistorySigma_le (d := d) Δ n s hs
    have htest := hkilled n (s.indicator (fun _ => (1 : ℝ)))
      (measurable_const.indicator hs) ⟨1, fun z => by
        by_cases hz : z ∈ s <;> simp [hz]⟩
    have htest' : (μ.restrict D).real s = (ν.restrict D).real s := by
      have h1 : (μ.restrict D).real s = ∫ z in D, (s.indicator (1 : CoupledSample d → ℝ)) z ∂μ := by
        simpa using (integral_indicator_one (s := s) hs').symm
      have h2 : ∫ z in D, (s.indicator (1 : CoupledSample d → ℝ)) z ∂μ =
                ∫ z in D, (s.indicator (1 : CoupledSample d → ℝ)) z ∂ν := by
        calc
          ∫ z in D, (s.indicator (1 : CoupledSample d → ℝ)) z ∂μ =
              ∫ z, Set.indicator D (s.indicator (1 : CoupledSample d → ℝ)) z ∂μ := by
            simpa using (integral_indicator hD).symm
          _ = ∫ z, Set.indicator D (s.indicator (1 : CoupledSample d → ℝ)) z ∂ν := htest
          _ = ∫ z in D, (s.indicator (1 : CoupledSample d → ℝ)) z ∂ν := by
            simpa using integral_indicator hD
      have h3 : ∫ z in D, (s.indicator (1 : CoupledSample d → ℝ)) z ∂ν = (ν.restrict D).real s := by
        simpa using integral_indicator_one (s := s) hs'
      rw [h1, h2, h3]
    exact (ENNReal.toReal_eq_toReal_iff' (measure_ne_top (μ.restrict D) s)
      (measure_ne_top (ν.restrict D) s)).mp htest'
  change (∫ z, Set.indicator D F z ∂μ) = ∫ z, Set.indicator D F z ∂ν
  rw [integral_indicator hD, integral_indicator hD, heq]

end EinsteinRelation.Regeneration
