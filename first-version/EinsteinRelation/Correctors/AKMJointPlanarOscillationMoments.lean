import EinsteinRelation.Correctors.AKMPlanarAllCenterScalarMoments
import EinsteinRelation.Correctors.AKMPlanarAllCenterFluxMoments
import EinsteinRelation.Correctors.AKMScalarGaugeProductionTransfer

/-! Source: `paper/main.tex:724-731`. Joint planar scalar and flux
representatives have radius-four heat-centered L² moments at every center.
The constant precedes the environment law and the coordinate direction. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The planar source representatives can be chosen jointly with their
canonical gradient identity and uniform local oscillation moments. -/
theorem exists_joint_planar_akm_oscillation_moments
    (h46 : ScalarPlanarL2Estimate) (h68 : FluxGradientEstimate)
    (h615 : FluxPlanarL2Estimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (L r₀ p : ℝ) (hL : 1 ≤ L) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw 2 L r₀) (i : Fin 2),
      ∃ φ : Corrector (actualCoefficientLaw Q) (halfDirection i),
        ∃ S : FluxCorrector (scaledAKMCorrector φ 2),
          (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec 2)),
            (2 : ℝ) • (halfDirection i + φ.grad
              (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
              (correctorUnitVector i + (canonicalCorrectorGradient Q i :
                Lp (EuclideanSpace ℝ (Fin 2)) 2 (reducedEnvironmentLaw Q))
                  (translate (r₀ • y) (reduce ω.1))).ofLp) ∧
          ∀ z : Vec 2,
            (∫⁻ a, ENNReal.ofReal ((Real.sqrt (⨍ x in ball z 4,
              |φ.potential a x - scalarHeatAverage (φ.potential a) z 4| ^ 2 ∂volume)) ^ p)
              ∂actualCoefficientLaw Q) ≤ ENNReal.ofReal C ∧
            (∫⁻ a, ENNReal.ofReal ((Real.sqrt (⨍ x in ball z 4,
              frobeniusNorm (S.potential a x -
                fluxHeatAverage (S.potential a) z 4) ^ 2 ∂volume)) ^ p)
              ∂actualCoefficientLaw Q) ≤ ENNReal.ofReal C := by
  letI : Fact (2 ≤ 2) := ⟨by norm_num⟩
  have hK : 1 < AKMUpperEllipticity L := by
    have hexp : 1 < Real.exp (2 * L) := Real.one_lt_exp_iff.mpr (by linarith)
    have hκ : 1 < ellipticityScale L := by
      unfold ellipticityScale
      nlinarith
    unfold AKMUpperEllipticity
    nlinarith
  obtain ⟨Cφ, hCφ, hφ⟩ := akm_planar_scalar_allCenter_L2_moments h46 L p hK hp
  obtain ⟨CS, hCS, hS⟩ := akm_planar_flux_allCenter_L2_moments h615 L p hK hp
  obtain ⟨_, _, hflux⟩ := akm_flux_gradient_L2_moments h68 2 (by norm_num)
    (AKMUpperEllipticity L) p hK hp
  let A := Cφ * (Real.sqrt (Real.log 4)) ^ p
  let B := CS * (Real.sqrt (Real.log 4)) ^ (p / 2)
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨A + B, add_pos hA hB, ?_⟩
  intro Q i
  obtain ⟨φ, hid⟩ := exists_akmCorrector_global_gradient_identification hP Q i
  obtain ⟨⟨S⟩, _⟩ := hflux (actualCoefficientLaw Q)
    (lawHypotheses_actualCoefficientLaw Q) ((2 : ℝ) • halfDirection i)
    (euclideanNorm_two_smul_halfDirection i) (scaledAKMCorrector φ 2)
  refine ⟨φ, S, hid, fun z => ⟨?_, ?_⟩⟩
  · exact (hφ Q i φ hid z 4 (by norm_num)).trans
      (ENNReal.ofReal_le_ofReal (by change A ≤ A + B; linarith))
  · exact (hS Q i φ hid S z 4 (by norm_num)).trans
      (ENNReal.ofReal_le_ofReal (by change B ≤ A + B; linarith))

end EinsteinRelation.Correctors
