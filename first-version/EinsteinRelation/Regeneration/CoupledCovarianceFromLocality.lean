import EinsteinRelation.Regeneration.CoupledSpatialCovariance
import EinsteinRelation.Diffusion.ReducedKernelTranslation
import EinsteinRelation.Calculus.HorizontalTranslationLp

/-! # Product-almost-everywhere covariance of the actual coupling

Source `paper/main.tex:406–408`. Stationarity transports the single good
environment set under the joint random endpoint translation. The fibre
argument preserves the separate origin and spatial-almost-everywhere clauses.
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinRelation.Regeneration

/-- Frozen GMP locality implies spatial covariance of the actual complete
coupled path/bit kernel with the product-almost-everywhere qualifier. -/
theorem coupled_spatial_covariance_of_gmp_locality
    (hLoc : External.GMPKernelLocality)
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : CoupledQuenchedLaws d)
    (hK : HasProbabilityLaws Q.measure K) (hm : HasPathMarginals Q.measure K P)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (δ R : ℝ) (hR : 0 < R) (i : Fin d)
    (hr : HasDeterministicRestart Q.measure Δ K)
    (hone : Renewal.HasOneIntervalKernel Q.measure Δ δ R i P K) :
    ∀ᵐ p ∂(volume : Measure (Vec d)).prod Q.measure,
      (K p).map (recenterSample p.1) = K (0, translate p.1 p.2) := by
  have hgood := ae_coupledEnvironmentRegular hd Q lam h0 h1 P K hK hm hP Δ hΔ δ R i hr hone
  have htrans : Measure.QuasiMeasurePreserving (fun p : Vec d × FieldPair d => translate p.1 p.2)
      ((volume : Measure (Vec d)).prod Q.measure) Q.measure :=
    MeasureTheory.QuasiMeasurePreserving.prod_of_right Probability.continuous_translate.measurable
      (Filter.Eventually.of_forall fun a =>
        (measurePreserving_translate Q.measure Q.stationary a).quasiMeasurePreserving)
  filter_upwards [Measure.quasiMeasurePreserving_snd.ae hgood, htrans.ae hgood,
    hK.2, hm.2, hr.2, hone.2] with p hg hg' hp hm hr ho
  have hx : CoupledFibreRegular Δ δ R i P K (p.1 + 0, p.2) := by
    simpa only [add_zero] using (show CoupledFibreRegular Δ δ R i P K p from ⟨hp, hm, hr, ho⟩)
  have hc := coupled_map_recenter_eq_of_regular hd Λ₀ Q.ellipticity_parameter lam h0 h1
    Δ hΔ δ R hR i P K p.1 0 p.2 (translate p.1 p.2) hg hg' hx hg'.2.1
  apply (by simpa only [add_zero] using hc :
    (∀ y : Vec d, (P (p.1 + y, p.2)).map (recenterPathEquiv p.1) = P (y, translate p.1 p.2)) →
      (K p).map (recenterSample p.1) = K (0, translate p.1 p.2))
  intro y
  obtain ⟨hω, r, hr⟩ := hg.1
  obtain ⟨hω', r', hr'⟩ := hg'.1
  rw [hr, hr']
  exact Diffusion.reduced_pathLaw_map_recenter_eq_of_realizations hLoc hd Λ₀
    Q.ellipticity_parameter lam h0 h1 p.2 p.1 hω hω' r r' y


end EinsteinRelation.Regeneration
