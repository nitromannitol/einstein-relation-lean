import EinsteinRelation.Correctors.AKMCarrierIdentificationCellFluxAssembly

/-! Source: `paper/main.tex:693-702,727-729`. The canonical gradient identity determines the literal spatial flux. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

theorem ae_akmFlux_eq_scaled_canonicalFlux
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (g : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d)
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      ((project (r₀ := r₀) Q.ellipticity_parameter ω) y).mulVec
          (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (ellipticityScale L / 2) •
          (canonicalCorrectorFlux Q i (translate (r₀ • y) (reduce ω.1))).ofLp := by
  have hσ : Measurable (fun y : Vec d => r₀ • y) :=
    (continuous_id.const_smul r₀).measurable
  have hsp := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_spatial_canonicalCorrectorFlux Q i (σ := fun y => r₀ • y) hσ)
  filter_upwards [hid, hsp] with ω hω hs
  filter_upwards [hω, hs] with y hy hsy
  change ((ellipticityScale L • (reduce ω.1).1 (r₀ • y)).mulVec
    (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y)) = _
  change _ = (ellipticityScale L / 2) • (canonicalCorrectorFlux Q i
    (translate (r₀ • y) (reduce ω.1))).ofLp
  rw [hsy, ← hy, Matrix.smul_mulVec, Matrix.mulVec_smul]
  ext j
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

end EinsteinRelation.Correctors
