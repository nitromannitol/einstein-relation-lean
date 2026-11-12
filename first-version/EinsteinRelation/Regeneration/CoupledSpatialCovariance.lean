import EinsteinRelation.Regeneration.CoupledHistoryHalfSpaceLocality
import EinsteinRelation.Regeneration.FirstHistoryTranslation
import EinsteinRelation.Regeneration.RestartTranslation
import EinsteinRelation.Regeneration.KilledBridgeTranslation
import EinsteinRelation.Regeneration.EndpointDensityTranslation
import EinsteinRelation.Regeneration.FiniteHistoryMeasureExt
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Spatial covariance of the complete coupled path/bit law

Source `paper/main.tex:406–408`. Diffusion covariance determines both
first-bit branches. Deterministic restart and positive-time densities
then determine all finite histories and hence the complete coupled law.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration

/-- Covariance of the diffusion implies covariance of its actual
coupling on regular fibres; no uniqueness of a coupled law is assumed. -/
theorem coupled_map_recenter_eq_of_regular {d : ℕ}
    (hd : 2 ≤ d) (Λ₀ : ℝ) (hΛ₀ : 1 ≤ Λ₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d) (a x : Vec d) (ω ω' : FieldPair d)
    (hg : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω)
    (hg' : CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K ω')
    (hx : CoupledFibreRegular Δ δ R i P K (a + x, ω))
    (hx' : CoupledFibreRegular Δ δ R i P K (x, ω'))
    (hPcov : ∀ y : Vec d, (P (a + y, ω)).map (recenterPathEquiv a) = P (y, ω')) :
    (K (a + x, ω)).map (recenterSample a) = K (x, ω') := by
  let Ka : CoupledQuenchedLaws d :=
    (K.comap (fun p : Vec d × FieldPair d => (a + p.1, p.2))
      ((measurable_const.add measurable_fst).prodMk measurable_snd)).map (recenterSampleEquiv a)
  have hKa : ∀ p, Ka p = (K (a + p.1, p.2)).map (recenterSampleEquiv a) := by
    intro p
    rw [Kernel.map_apply _ (recenterSampleEquiv a).measurable, Kernel.comap_apply]
  have hstart : ∀ (η : FieldPair d),
      CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K η →
      ∀ y, (K (y, η)).map Prod.fst = P (y, η) → ∀ᵐ z ∂K (y, η), z.1 0 = y := by
    intro η hη y hm
    obtain ⟨_, r, hr⟩ := hη.1
    have h := r.pathLaw_starts_at y
    rw [← hr y, ← hm] at h
    exact ae_of_ae_map measurable_fst.aemeasurable h
  have hprobP : ∀ (η : FieldPair d),
      CoupledEnvironmentRegular hd Λ₀ hΛ₀ lam h0 h1 Δ δ R i P K η →
      ∀ y, IsProbabilityMeasure (P (y, η)) := by
    intro η hη y
    obtain ⟨_, r, hr⟩ := hη.1
    rw [hr y]
    haveI := r.pathLaw_isMarkovKernel
    infer_instance
  have hcompare : ∀ y,
      CoupledFibreRegular Δ δ R i P K (a + y, ω) →
      CoupledFibreRegular Δ δ R i P K (y, ω') →
      ∀ F : CoupledSample d → ℝ,
        @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F →
        BoundedRealTest F → (∫ z, F z ∂Ka (y, ω)) = ∫ z, F z ∂K (y, ω') := by
    intro y hy hy' F hF hb
    haveI := hy.1
    haveI := hy'.1
    haveI := hprobP ω hg (a + y)
    haveI := hprobP ω' hg' y
    rw [hKa, integral_map_equiv]
    exact integral_first_history_comp_recenter_of_segment_maps Δ δ R i P P K K
      (a + y, ω) (y, ω') a (hstart ω hg _ hy.2.1) (hstart ω' hg' _ hy'.2.1)
      hy.2.2.2 hy'.2.2.2 (hPcov y)
      (map_recenter_killedBridgeMixture Δ R hR i P P a y ω ω' (hPcov y)) F hF hb
  haveI := hx.1
  haveI := hx'.1
  haveI : IsProbabilityMeasure (Ka (x, ω)) := by
    rw [hKa]
    exact Measure.isProbabilityMeasure_map (recenterSampleEquiv a).measurable.aemeasurable
  have hsp : ∀ᵐ y ∂(volume : Measure (Vec d)),
      IsProbabilityMeasure (Ka (y, ω)) ∧ IsProbabilityMeasure (K (y, ω')) ∧
      (y ∈ (Set.univ : Set (Vec d)) → ∀ F : CoupledSample d → ℝ,
        @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ 1) inferInstance F →
        BoundedRealTest F →
        (∀ z, F z ≠ 0 → z ∈ Probability.historyStays Δ 1 Set.univ) →
        (∫ z, F z ∂Ka (y, ω)) = ∫ z, F z ∂K (y, ω')) := by
    filter_upwards [(measurePreserving_add_left (volume : Measure (Vec d)) a).quasiMeasurePreserving.ae
      hg.2.2.1, hg'.2.2.1] with y hy hy'
    haveI := hy.1
    refine ⟨?_, hy'.1, fun _ F hF hb _ => hcompare y hy hy' F hF hb⟩
    rw [hKa]
    exact Measure.isProbabilityMeasure_map (recenterSampleEquiv a).measurable.aemeasurable
  have hhist := integral_supported_histories_eq_of_first_interval_eq Δ hΔ Set.univ isClosed_univ
    Ka K (x, ω) (x, ω')
    (deterministicRestartAt_conjugate_spatial Δ K a x ω hx.2.2.1) hx'.2.2.1
    (fun F hF hb _ => hcompare x hx hx' F hF hb) hsp
    (fun n hn => by
      rw [hKa]
      exact map_recenterSample_endpoint_absolutelyContinuous _ a _
        (coupled_endpoint_density_of_path_marginal P K (a + x, ω) hx.2.1 _
          (hg.2.2.2 n hn (a + x))))
    (fun n hn => coupled_endpoint_density_of_path_marginal P K (x, ω') hx'.2.1 _
      (hg'.2.2.2 n hn x))
  have heq : Ka (x, ω) = K (x, ω') :=
    measure_eq_of_finite_history_integrals _ _ Δ hΔ (fun n hn F hF hb =>
      hhist n hn F hF hb (fun _ _ _ _ => Set.mem_univ _))
  simpa only [hKa, recenterSampleEquiv_apply] using heq


end EinsteinRelation.Regeneration
