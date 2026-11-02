import EinsteinRelation.Correctors.AKMCoefficientFactorOrbits
import EinsteinRelation.Correctors.SpatialCovarianceCongruence

/-!
# Stationarity from the actual canonical gradient identity

Source: `paper/main.tex:693-702`. Any jointly measurable gradient with
the canonical spatial identification agrees with the explicitly covariant
coefficient-factor representative. Translation invariance transports this
agreement to both sides of the stationarity identity.
-/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The explicit covariant candidate has the canonical affine-gradient
identity for each chosen measurable reconstruction and coefficient factor. -/
theorem akmGradientFromCoefficientFactor_canonical_identification
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (R : Coefficient d (AKMUpperEllipticity L) → CoefficientField d)
    (hReq : ∀ (a : Coefficient d (AKMUpperEllipticity L)) (ha : Continuous a.field),
      R a = ⟨a.field, ha⟩)
    (F : CoefficientField d → EuclideanSpace ℝ (Fin d)) (hF : StronglyMeasurable F)
    (hFG : (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) =ᵐ[reducedEnvironmentLaw Q]
        fun ω => F ω.1) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i +
        akmGradientFromCoefficientFactor r₀ R F
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp := by
  have h := ae_akmUnscaledCoefficientFactor_project Q R hReq
    (canonicalCorrectorGradient Q i : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (Lp.stronglyMeasurable _).measurable F hF.measurable hFG
  have hr : r₀ ≠ 0 := (zero_lt_one.trans_le Q.range_parameter).ne'
  filter_upwards [h] with ω hω
  have hscaled := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d)) hr).ae hω
  filter_upwards [hscaled] with y hy
  change (2 : ℝ) • (halfDirection i + (1 / 2 : ℝ) •
    (akmUnscaledCoefficientFactor r₀ R F
      (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀ • y)).ofLp) = _
  rw [← hy]
  ext j
  by_cases hj : j = i <;> simp [halfDirection, correctorUnitVector, unitVector,
    PiLp.add_apply, hj]
  all_goals ring

/-- The AKM stationarity field follows from joint measurability and the
canonical affine-gradient identity alone. -/
theorem ae_akm_stationary_of_canonical_gradient
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (g : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g p.1 p.2))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (z : Vec d) :
    ∀ᵐ a ∂actualCoefficientLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      g a (x + z) = g (translateCoefficient z a) x := by
  obtain ⟨R, hR, hReq⟩ := exists_measurable_continuous_reconstruction
    (d := d) (K := AKMUpperEllipticity L)
  obtain ⟨F, hF, hFG⟩ := exists_coefficient_factor_of_canonicalGradient Q i
  let h := akmGradientFromCoefficientFactor (d := d) (L := L) r₀ R F
  have hm := measurable_akmGradientFromCoefficientFactor (d := d) (L := L) r₀ R hR F hF
  have hc := akmGradientFromCoefficientFactor_canonical_identification Q i R hReq F hF hFG
  have heq : ∀ᵐ a ∂actualCoefficientLaw Q, (fun x => g a x) =ᵐ[volume] (fun x => h a x) := by
    apply ae_spatial_eq_of_map_pullback (physicalReferenceLaw Q) volume
      (project (r₀ := r₀) Q.ellipticity_parameter) (measurable_project Q.ellipticity_parameter)
      g h hg hm
    filter_upwards [hid, hc] with ω hω hcω
    filter_upwards [hω, hcω] with x hx hcx
    have hh := hx.trans hcx.symm
    ext j
    have hj := congrArg (fun v : Vec d => v j) hh
    simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at hj
    linarith
  exact ae_spatial_covariance_congr (actualCoefficientLaw Q) (translateCoefficient z)
    ⟨measurable_translateCoefficient z, actualCoefficientLaw_translation_invariant_real Q z⟩
    z g h heq (ae_akmGradientFromCoefficientFactor_covariance Q R hR hReq F hF z)

end EinsteinRelation.Correctors
