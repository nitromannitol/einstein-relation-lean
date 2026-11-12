import EinsteinRelation.Regeneration.KilledFutureCovariance

/-!
# Transporting killed future locality to spatial starting points

Source `paper/main.tex:383–409`. Locality at the origin and spatial-a.e.
covariance suffice for the versions used after Fubini. The origin locality
premise is an internal joint-test obligation, not a frozen external input.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Regeneration

/-- Locality of the killed joint future test at the origin transports to
the corrected future half-space for spatial-almost every starting point. -/
theorem exists_killed_future_local_versions_of_covariance {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (K : CoupledQuenchedLaws d) (R : ℝ) (i : Fin d)
    (Φ : FutureState d i R → ℝ) (hΦ : Measurable Φ)
    (B : Vec d × FieldPair d → ℝ)
    (hBp : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q,
      B xω = ∫ z, killedFutureTest R i Φ (xω, z) ∂K xω)
    (A : FieldPair d → ℝ)
    (hA : Measurable[localSigma {x : Vec d | -2 * R ≤ x i}] A)
    (hAo : ∀ᵐ ω ∂Q, A ω = ∫ z, killedFutureTest R i Φ ((0, ω), z) ∂K (0, ω))
    (hcov : ∀ᵐ xω ∂(volume : Measure (Vec d)).prod Q,
      (K xω).map (recenterSample xω.1) = K (0, translate xω.1 xω.2)) :
    ∀ᵐ y ∂(volume : Measure (Vec d)), ∃ A' : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | y i - 2 * R ≤ x i}] A' ∧
      (fun ω => B (y, ω)) =ᵐ[Q] A' := by
  have hp := Measure.ae_ae_of_ae_prod hBp
  have hc := Measure.ae_ae_of_ae_prod hcov
  filter_upwards [hp, hc] with y hyp hyc
  refine ⟨fun ω => A (translate y ω), ?_, ?_⟩
  · apply (hA.comp (Probability.measurable_translate_local y _)).mono
      (Probability.localSigma_mono ?_) le_rfl
    rintro x ⟨z, hz, rfl⟩
    change -2 * R ≤ z i at hz
    change y i - 2 * R ≤ (y + z) i
    simp only [Pi.add_apply]
    linarith
  · have ht : ∀ᵐ ω ∂Q,
        A (translate y ω) = ∫ z, killedFutureTest R i Φ ((0, translate y ω), z)
          ∂K (0, translate y ω) :=
      ae_of_ae_map (Probability.measurable_translate y).aemeasurable (by rw [hQ y]; exact hAo)
    filter_upwards [hyp, hyc, ht] with ω hω hcω htω
    have hmrec : Measurable (recenterSample y) :=
      (measurable_recenterSample (d := d)).comp (measurable_const.prodMk measurable_id)
    have hmtest : Measurable (fun z => killedFutureTest R i Φ ((0, translate y ω), z)) :=
      (measurable_killedFutureTest R i Φ hΦ).comp (measurable_const.prodMk measurable_id)
    rw [hω, htω, ← hcω, integral_map hmrec.aemeasurable hmtest.aestronglyMeasurable]
    exact integral_congr_ae (Filter.Eventually.of_forall fun z =>
      (killedFutureTest_recenter R i Φ y ω z).symm)


end EinsteinRelation.Regeneration
