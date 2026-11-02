import EinsteinRelation.Regeneration.OneIntervalLocality
import EinsteinRelation.Regeneration.EndpointAverageFubini

/-!
# The excluded successful-bridge case in past half-space locality

Source `paper/main.tex:377`. The endpoint law of the literal bridge
mixture is dominated by the conditional uniform endpoint law. Hence the
mixture charges only endpoints in the endpoint ball, even without an
extra positivity or absolute-continuity assumption. A past-barrier test
therefore vanishes for the high starting-point case of Step 2.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

noncomputable section

namespace EinsteinRelation.Regeneration

/-- Endpoint reweighting cannot put mass outside the prescribed uniform
endpoint law. The inequality also covers any singular part of that law. -/
theorem map_killedBridgeMixture_endpoint_le_uniform {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) :
    (Renewal.killedBridgeMixture Δ R i P z ω).map (fun γ : Path d => γ Δ) ≤
      cond (volume : Measure (Vec d)) (endpointBall i R z) := by
  let μ := Renewal.killedSegmentLaw Δ R i P z ω
  let e : Path d → Vec d := fun γ => γ Δ
  let η := cond (volume : Measure (Vec d)) (endpointBall i R z)
  have he : Measurable e := (continuous_eval_const Δ).measurable
  have hg : Measurable (η.rnDeriv (μ.map e)) := Measure.measurable_rnDeriv _ _
  have hm : (μ.withDensity ((η.rnDeriv (μ.map e)) ∘ e)).map e =
      (μ.map e).withDensity (η.rnDeriv (μ.map e)) := by
    apply Measure.ext
    intro s hs
    rw [Measure.map_apply he hs, withDensity_apply _ (he hs), withDensity_apply _ hs,
      setLIntegral_map hs hg he]
    rfl
  change (μ.withDensity ((η.rnDeriv (μ.map e)) ∘ e)).map e ≤ η
  rw [hm]
  exact Measure.withDensity_rnDeriv_le _ _

/-- The exact bridge mixture has its endpoint in the source endpoint
ball almost surely. No source result about coupling locality is assumed. -/
theorem ae_killedBridgeMixture_endpoint_mem {d : ℕ}
    (Δ : ℝ≥0) (R : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) :
    ∀ᵐ γ ∂Renewal.killedBridgeMixture Δ R i P z ω, γ Δ ∈ endpointBall i R z := by
  have hB : MeasurableSet (endpointBall i R z) :=
    (measurableSet_endpointBall_pair i R).preimage (measurable_const.prodMk measurable_id)
  have hcond : ∀ᵐ y ∂cond (volume : Measure (Vec d)) (endpointBall i R z),
      y ∈ endpointBall i R z := Measure.ae_smul_measure (ae_restrict_mem hB) _
  have hmap := (Measure.absolutelyContinuous_of_le
    (map_killedBridgeMixture_endpoint_le_uniform Δ R i P z ω)).ae_le hcond
  exact ae_of_ae_map (continuous_eval_const Δ).measurable.aemeasurable hmap

/-- If a segment test requires the path to remain below the past barrier,
the successful bridge from a high starting point contributes zero. This
is the first alternative of the one-interval argument in Step 2. -/
theorem integral_killedBridgeMixture_eq_zero_of_past_barrier {d : ℕ}
    (Δ : ℝ≥0) (R v : ℝ) (i : Fin d) (P : QuenchedPathLaws d)
    (z : Vec d) (ω : FieldPair d) (hz : v - 8 * R ≤ z i)
    (F : Path d → ℝ)
    (hsupport : ∀ γ, F γ ≠ 0 → ∀ t : ℝ≥0, t ≤ Δ → γ t i ≤ v) :
    (∫ γ, F γ ∂Renewal.killedBridgeMixture Δ R i P z ω) = 0 := by
  have hzero : F =ᵐ[Renewal.killedBridgeMixture Δ R i P z ω] 0 := by
    filter_upwards [ae_killedBridgeMixture_endpoint_mem Δ R i P z ω] with γ hγ
    change F γ = 0
    by_contra hne
    have hbelow := hsupport γ hne Δ le_rfl
    have habove := endpointBall_subset_above_past_barrier i R v z hz hγ
    exact (not_lt_of_ge hbelow) habove
  simpa only [Pi.zero_apply, integral_zero] using integral_congr_ae hzero


end EinsteinRelation.Regeneration
