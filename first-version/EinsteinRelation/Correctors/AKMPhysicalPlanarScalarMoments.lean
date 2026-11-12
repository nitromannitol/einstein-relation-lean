import EinsteinRelation.Correctors.ScalarPhysicalHeatGaugeL2
import EinsteinRelation.Correctors.AKMPlanarOscillationMeasurability

/-! Source: `paper/main.tex:724-731`. The planar scalar estimate on the
actual physical law, with the local heat gauge and canonical amplitude. -/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The physical planar scalar local L² moment is uniform over all
centers, laws and coordinate directions. Its heat gauge is at radius
`4r₀`, and the amplitude is the canonical `2r₀`. -/
theorem akm_planar_physical_scalar_local_L2_moments
    (h46 : ScalarPlanarL2Estimate) (L r₀ p : ℝ)
    (hK : 1 < AKMUpperEllipticity L) (hr₀ : 1 ≤ r₀) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (i : Fin 2)
      (φ : Corrector (actualCoefficientLaw Q) (halfDirection i)),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec 2)),
        (2 : ℝ) • (halfDirection i + φ.grad
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
          (correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
              (translate (r₀ • y) (reduce ω.1))).ofLp) →
      ∀ z : Vec 2,
        (∫⁻ ω, ENNReal.ofReal ((Real.sqrt (∫ x in ball z 4,
          |(2 * r₀) * φ.potential
              (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) -
            scalarHeatAverage (fun y => (2 * r₀) * φ.potential
              (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • y)) z
                (r₀ * 4)| ^ 2 ∂volume)) ^ p) ∂physicalReferenceLaw Q) ≤
          ENNReal.ofReal C := by
  obtain ⟨C₀, hC₀, hest⟩ := akm_planar_scalar_allCenter_L2_moments h46 L p hK hp
  let A := (Real.sqrt ((2 * r₀) ^ 2 * r₀ ^ 2)) ^ p
  let B := (Real.sqrt (volume.real (ball (0 : Vec 2) 4))) ^ p
  let D := C₀ * (Real.sqrt (Real.log 4)) ^ p
  have hr0 : 0 < r₀ := zero_lt_one.trans_le hr₀
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := Real.rpow_pos_of_pos
    (Real.sqrt_pos.mpr (ball_volume_pos_finite 2 4 (by norm_num))) _
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨A * (B * D), mul_pos hA (mul_pos hB hD), ?_⟩
  intro Q i φ hid z
  have hu : ∀ᵐ a ∂actualCoefficientLaw Q, ∀ R : ℝ, 0 < R →
      MemLp (φ.potential a) 2 (volume.restrict (ball 0 R)) :=
    φ.locally_square_integrable.mono fun a ha R hR => (ha R hR).1
  have h := scalar_physical_heat_gauge_local_L2_moment
    (measurePreserving_akmProject Q) φ.potential hu r₀ (2 * r₀) p hr₀ hp.le z
    (aemeasurable_planar_scalar_oscillation h46 hK Q i φ hid (r₀⁻¹ • z) 4 (by norm_num))
    (ENNReal.ofReal D) (hest Q i φ hid (r₀⁻¹ • z) 4 (by norm_num))
  simpa only [A, B, ENNReal.ofReal_mul hA.le, ENNReal.ofReal_mul hB.le] using h

end EinsteinRelation.Correctors
