import EinsteinRelation.Correctors.AKMPhysicalPlanarScalarMoments
import EinsteinRelation.Correctors.AKMPhysicalPlanarFluxMoments
import EinsteinRelation.Correctors.AKMJointPlanarOscillationMoments

/-! Source: `paper/main.tex:724-731`. Joint planar physical scalar and
flux representatives with uniform heat-gauged radius-four L² moments. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Both physical local L² moments are uniform in the law, coordinate
and center, with one constant preceding all those choices. This retains
the raw source heat selection; identification with the physical canonical
flux gradient requires the separate cutoff transport argument. -/
theorem exists_physical_planar_local_L2_moments
    (h46 : ScalarPlanarL2Estimate) (h68 : FluxGradientEstimate)
    (h615 : FluxPlanarL2Estimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (L r₀ p : ℝ) (hL : 1 ≤ L) (hr₀ : 1 ≤ r₀) (hp : 0 < p) :
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
            (∫⁻ ω, ENNReal.ofReal ((Real.sqrt (∫ x in ball z 4,
              |(2 * r₀) * φ.potential
                  (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) -
                scalarHeatAverage (fun y => (2 * r₀) * φ.potential
                  (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • y)) z
                    (r₀ * 4)| ^ 2 ∂volume)) ^ p) ∂physicalReferenceLaw Q) ≤
                      ENNReal.ofReal C ∧
            (∫⁻ ω, ENNReal.ofReal ((Real.sqrt (∫ x in ball z 4,
              frobeniusNorm ((r₀ / ellipticityScale L) • S.potential
                  (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) -
                fluxHeatAverage (fun y => (r₀ / ellipticityScale L) • S.potential
                  (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • y)) z
                    (r₀ * 4)) ^ 2 ∂volume)) ^ p) ∂physicalReferenceLaw Q) ≤
                      ENNReal.ofReal C := by
  have hK : 1 < AKMUpperEllipticity L := by
    have hexp : 1 < Real.exp (2 * L) := Real.one_lt_exp_iff.mpr (by linarith)
    have hκ : 1 < ellipticityScale L := by
      unfold ellipticityScale
      nlinarith
    unfold AKMUpperEllipticity
    nlinarith
  obtain ⟨Cφ, hCφ, hφ⟩ := akm_planar_physical_scalar_local_L2_moments
    h46 L r₀ p hK hr₀ hp
  obtain ⟨CS, hCS, hS⟩ := akm_planar_physical_flux_local_L2_moments
    h615 L r₀ p hK hL hr₀ hp
  obtain ⟨_, _, hobjects⟩ := exists_joint_planar_akm_oscillation_moments
    h46 h68 h615 hP L r₀ p hL hp
  refine ⟨Cφ + CS, add_pos hCφ hCS, ?_⟩
  intro Q i
  obtain ⟨φ, S, hid, _⟩ := hobjects Q i
  refine ⟨φ, S, hid, fun z => ⟨?_, ?_⟩⟩
  · exact (hφ Q i φ hid z).trans (ENNReal.ofReal_le_ofReal (by linarith))
  · exact (hS Q i φ hid S z).trans (ENNReal.ofReal_le_ofReal (by linarith))

end EinsteinRelation.Correctors
