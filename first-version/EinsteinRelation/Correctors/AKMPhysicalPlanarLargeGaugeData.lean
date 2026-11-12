import EinsteinRelation.Correctors.AKMPlanarScalarLargeGaugeMajorant
import EinsteinRelation.Correctors.AKMPlanarFluxLargeGaugeMajorant
import EinsteinRelation.Correctors.PhysicalScalarMajorant
import EinsteinRelation.Correctors.PhysicalTensorMajorant
import EinsteinRelation.Correctors.AKMLocalCorrectorSpecialization
import EinsteinRelation.Correctors.AKMPhysicalPotentials
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3
/-- Source: `paper/main.tex:718-723,743-745`. Radius-four physical majorants
in one heat gauge shared by the entire large ball. -/
theorem exists_physical_planar_largeGauge_local_majorants
    (h46 : ScalarPlanarL2Estimate) (h47 : ScalarHeatDifferenceEstimate)
    (h615 : FluxPlanarL2Estimate) (h616 : FluxHeatDifferenceEstimate)
    (L r₀ p : ℝ) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hp : 2 ≤ p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (i : Fin 2)
      (φ : Corrector (actualCoefficientLaw Q) (halfDirection i)),
      CanonicalAKMGradientIdentification Q i φ →
      ∀ (S : FluxCorrector (scaledAKMCorrector φ 2)) (R : ℝ), 1 ≤ R → ∀ y z : Vec 2,
      euclideanNorm (z - y) ≤ 2 * R + 4 →
      let c : PhysicalField 2 L → ℝ := fun ω => (2 * r₀) *
        scalarHeatAverage (φ.potential (project (r₀ := r₀) Q.ellipticity_parameter ω))
          (r₀⁻¹ • y) (8 * R)
      let b : PhysicalField 2 L → Mat 2 := fun ω => (r₀ / ellipticityScale L) •
        fluxHeatAverage (S.potential (project (r₀ := r₀) Q.ellipticity_parameter ω))
          (r₀⁻¹ • y) (8 * R)
      ∃ U V : PhysicalField 2 L → ℝ,
        AEMeasurable U (physicalReferenceLaw Q) ∧
        AEMeasurable V (physicalReferenceLaw Q) ∧
        (∀ ω, 0 ≤ U ω) ∧ (∀ ω, 0 ≤ V ω) ∧
        (∀ᵐ ω ∂physicalReferenceLaw Q,
          Real.sqrt (∫ x in ball z 4, |physicalAKMScalarPotential Q φ ω x - c ω| ^ 2 ∂volume) ≤ U ω ∧
          Real.sqrt (∫ x in ball z 4,
            frobeniusNorm (physicalAKMFluxPotential Q φ S ω x - b ω) ^ 2 ∂volume) ≤ V ω) ∧
        (∫⁻ ω, ENNReal.ofReal (U ω ^ p) ∂physicalReferenceLaw Q) ≤
          ENNReal.ofReal (C * (Real.sqrt (Real.log (2 + R))) ^ p) ∧
        (∫⁻ ω, ENNReal.ofReal (V ω ^ p) ∂physicalReferenceLaw Q) ≤
          ENNReal.ofReal (C * (Real.sqrt (Real.log (2 + R))) ^ p) := by
  obtain ⟨C₁, hC₁, hscalar⟩ := akm_planar_scalar_large_heat_gauge_L2_majorant
    h46 h47 L p (one_lt_AKMUpperEllipticity hL) hp
  obtain ⟨C₂, hC₂, htensor⟩ := akm_planar_flux_large_heat_gauge_L2_majorant
    h615 h616 L p (one_lt_AKMUpperEllipticity hL) hp
  let A := (Real.sqrt ((2 * r₀) ^ 2 * r₀ ^ 2)) ^ p
  let B := (Real.sqrt ((r₀ / ellipticityScale L) ^ 2 * r₀ ^ 2)) ^ p
  have hA : 0 ≤ A := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  have hB : 0 ≤ B := Real.rpow_nonneg (Real.sqrt_nonneg _) _
  refine ⟨A * C₁ + B * C₂ + 1, by positivity, ?_⟩
  intro Q i φ hid S R hR y z hzy
  obtain ⟨M, hm, hm0, hmb, hmB⟩ := hscalar Q i φ hid r₀ R hr₀ hR z y hzy
  obtain ⟨N, hn, hn0, hnb, hnB⟩ := htensor Q i φ hid S r₀ R hr₀ hR z y hzy
  have hu := φ.locally_square_integrable.mono fun a ha t ht => (ha t ht).1
  have hS := S.locally_square_integrable.mono fun a ha t ht j k => (ha t ht j k).1
  obtain ⟨U, huM, hu0, hub, huB⟩ := physical_scalar_L2_majorant_of_raw_majorant
    (measurePreserving_akmProject Q) φ.potential
    (fun a => scalarHeatAverage (φ.potential a) (r₀⁻¹ • y) (8 * R))
    hu r₀ (2 * r₀) p hr₀ (by linarith) z M hm hm0 hmb _ hmB
  obtain ⟨V, hvM, hv0, hvb, hvB⟩ := physical_tensor_L2_majorant_of_raw_majorant
    (measurePreserving_akmProject Q) S.potential
    (fun a => fluxHeatAverage (S.potential a) (r₀⁻¹ • y) (8 * R))
    hS r₀ (r₀ / ellipticityScale L) p hr₀ (by linarith) z N hn hn0 hnb _ hnB
  refine ⟨U, V, huM, hvM, hu0, hv0, ?_, ?_, ?_⟩
  · filter_upwards [hub, hvb] with ω hω hω'
    exact ⟨hω, hω'⟩
  · apply huB.trans
    rw [max_eq_left (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    change A * (C₁ * _) ≤ _
    calc
      _ = (A * C₁) * (Real.sqrt (Real.log (2 + R))) ^ p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hB hC₂.le])
        (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
  · apply hvB.trans
    rw [max_eq_left (by positivity)]
    apply ENNReal.ofReal_le_ofReal
    change B * (C₂ * _) ≤ _
    calc
      _ = (B * C₂) * (Real.sqrt (Real.log (2 + R))) ^ p := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hA hC₁.le])
        (Real.rpow_nonneg (Real.sqrt_nonneg _) _)
end EinsteinRelation.Correctors
