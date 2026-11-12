import EinsteinRelation.Correctors.FluxPhysicalHeatGaugeL2
import EinsteinRelation.Correctors.AKMPlanarFluxOscillationMeasurability
import EinsteinRelation.Correctors.AKMPlanarAllCenterFluxMoments

/-! Source: `paper/main.tex:724-731`. The planar flux estimate on the
actual physical law, with the local heat gauge and canonical amplitude. -/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The physical planar flux local L² moment is uniform over all
centers, laws and coordinate directions. Its heat gauge is at radius
`4r₀`, and the amplitude is the canonical `r₀ / ellipticityScale L`. -/
theorem akm_planar_physical_flux_local_L2_moments
    (h615 : FluxPlanarL2Estimate) (L r₀ p : ℝ)
    (hK : 1 < AKMUpperEllipticity L) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (i : Fin 2)
      (φ : Corrector (actualCoefficientLaw Q) (halfDirection i)),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec 2)),
        (2 : ℝ) • (halfDirection i + φ.grad
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
              (translate (r₀ • y) (reduce ω.1))).ofLp) →
      ∀ (S : FluxCorrector (scaledAKMCorrector φ 2)) (z : Vec 2),
        (∫⁻ ω, ENNReal.ofReal ((Real.sqrt (∫ x in ball z 4,
          frobeniusNorm ((r₀ / ellipticityScale L) • S.potential
              (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) -
            fluxHeatAverage (fun y => (r₀ / ellipticityScale L) • S.potential
              (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • y)) z
                (r₀ * 4)) ^ 2 ∂volume)) ^ p) ∂physicalReferenceLaw Q) ≤
          ENNReal.ofReal C := by
  obtain ⟨C₀, hC₀, hest⟩ := akm_planar_flux_allCenter_L2_moments h615 L p hK hp
  let A := (Real.sqrt ((r₀ / ellipticityScale L) ^ 2 * r₀ ^ 2)) ^ p
  let B := (Real.sqrt (volume.real (ball (0 : Vec 2) 4))) ^ p
  let D := C₀ * (Real.sqrt (Real.log 4)) ^ (p / 2)
  have hr0 : 0 < r₀ := zero_lt_one.trans_le hr₀
  have hκ : 0 < ellipticityScale L := ellipticityScale_pos hL
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := Real.rpow_pos_of_pos
    (Real.sqrt_pos.mpr (ball_volume_pos_finite 2 4 (by norm_num))) _
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨A * (B * D), mul_pos hA (mul_pos hB hD), ?_⟩
  intro Q i φ hid S z
  have hu : ∀ᵐ a ∂actualCoefficientLaw Q, ∀ R : ℝ, 0 < R → ∀ j k,
      MemLp (fun x => S.potential a x j k) 2 (volume.restrict (ball 0 R)) :=
    S.locally_square_integrable.mono fun a ha R hR j k => (ha R hR j k).1
  have hc : ∀ᵐ a ∂actualCoefficientLaw Q, ∀ᵐ x ∂(volume : Measure (Vec 2)),
      (scaledAKMCorrector φ 2).grad (translateCoefficient (-(r₀⁻¹ • z)) a)
        (x + r₀⁻¹ • z) = (scaledAKMCorrector φ 2).grad a x := by
    filter_upwards [ae_inverse_translated_canonicalAKMGradient Q i φ hid (r₀⁻¹ • z)] with a ha
    filter_upwards [ha] with x hx
    change (2 : ℝ) • φ.grad (translateCoefficient (-(r₀⁻¹ • z)) a) (x + r₀⁻¹ • z) =
      2 • φ.grad a x
    rw [hx]
  have hm := aemeasurable_planar_flux_oscillation h615 hK (actualCoefficientLaw Q)
    (lawHypotheses_actualCoefficientLaw Q) ((2 : ℝ) • halfDirection i)
    (euclideanNorm_two_smul_halfDirection i) (scaledAKMCorrector φ 2) S (r₀⁻¹ • z)
    (measurePreserving_actualCoefficientTranslation Q (r₀⁻¹ • z))
    (measurePreserving_actualCoefficientTranslation Q (-(r₀⁻¹ • z))) hc 4 (by norm_num)
  have h := flux_physical_heat_gauge_local_L2_moment
    (measurePreserving_akmProject Q) S.potential hu r₀ (r₀ / ellipticityScale L) p hr₀ hp.le z
    hm.sqrt (ENNReal.ofReal D) (hest Q i φ hid S (r₀⁻¹ • z) 4 (by norm_num))
  simpa only [A, B, ENNReal.ofReal_mul hA.le, ENNReal.ofReal_mul hB.le] using h

end EinsteinRelation.Correctors
