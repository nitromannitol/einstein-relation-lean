import EinsteinRelation.Correctors.AKMHeatTimeDilation
import EinsteinRelation.Correctors.AKMUnitFluxConstruction
import EinsteinRelation.Correctors.AKMHeatFormulaOperations

/-!
# The physical canonical source in the rescaled heat formula

Source: `paper/main.tex:722,741-756`. This applies the kernel identities
to the actual canonical centered flux, including its coefficient scale
and the physical range. No selection-limit or potential-uniqueness
assumption is introduced.
-/
open MeasureTheory
open Set
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3
open HeatSelectedSkewMeaning

/-- The canonical physical source equals the inverse-scaled raw source on
all of space almost everywhere. -/
theorem ae_canonicalCenteredFlux_eq_rescaled_unitAKMSource
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hsource : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      centeredFlux (scaledAKMCorrector φ 2)
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
          ellipticityScale L •
            ((canonicalCorrectorFlux Q i (translate (r₀ • y) (reduce ω.1))).ofLp -
              (expectedCorrectorFlux Q i).ofLp)) :
    ∀ᵐ ω ∂physicalReferenceLaw Q,
      (fun x => (canonicalCorrectorFlux Q i (translate x (reduce ω.1)) -
        expectedCorrectorFlux Q i).ofLp) =ᵐ[volume]
      (fun x => (ellipticityScale L)⁻¹ •
        centeredFlux (scaledAKMCorrector φ 2)
          (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  have hκ := (ellipticityScale_pos Q.ellipticity_parameter).ne'
  filter_upwards [hsource] with ω hω
  have hx := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (inv_ne_zero hr.ne')).ae hω
  filter_upwards [hx] with x hxx
  simp only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at hxx
  rw [hxx, smul_smul, inv_mul_cancel₀ hκ, one_smul]
  rfl

/-- The actual canonical heat truncation, expressed with the raw
unit-direction AKM source. Both time endpoints retain the exact inverse
square range factor. -/
theorem ae_canonicalHeatTruncation_eq_rescaled_unitAKMSource
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hsource : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      centeredFlux (scaledAKMCorrector φ 2)
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
          ellipticityScale L •
            ((canonicalCorrectorFlux Q i (translate (r₀ • y) (reduce ω.1))).ofLp -
              (expectedCorrectorFlux Q i).ofLp)) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ (m n : ℕ) (j k l : Fin d) (x : Vec d),
      iteratedAKMHeatGradientTruncation
        (fun y => (canonicalCorrectorFlux Q i (translate y (reduce ω.1)) -
          expectedCorrectorFlux Q i).ofLp) m n j k l x =
      (ellipticityScale L)⁻¹ *
        ∫ t in Icc ((r₀ ^ 2)⁻¹ * ((m + 1 : ℕ) : ℝ)⁻¹)
          ((r₀ ^ 2)⁻¹ * ((n + 1 : ℕ) : ℝ)),
          akmHeatGradientSpaceIntegral
            (centeredFlux (scaledAKMCorrector φ 2)
              (project (r₀ := r₀) Q.ellipticity_parameter ω)) t j k l (r₀⁻¹ • x) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  filter_upwards [ae_canonicalCenteredFlux_eq_rescaled_unitAKMSource Q i φ hsource]
    with ω hω
  intro m n j k l x
  rw [iteratedAKMHeatGradientTruncation_congr_ae hω]
  have h := iteratedAKMHeatGradientTruncation_dilation
    (centeredFlux (scaledAKMCorrector φ 2)
      (project (r₀ := r₀) Q.ellipticity_parameter ω))
    r₀ (ellipticityScale L)⁻¹ hr m n j k l (r₀⁻¹ • x)
  simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using h

end EinsteinRelation.Correctors
