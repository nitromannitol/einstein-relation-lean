import EinsteinRelation.Correctors.AKMCorrectorDirectionScaling
import EinsteinRelation.Correctors.AKMCenteredFluxTransfer
import EinsteinRelation.Correctors.AKMStationaryCellMoments

/-!
# Unit-direction raw flux correctors on the actual coefficient law

Source: `paper/main.tex:722-731,741-747`. The canonical scalar gradient
first gives an AKM corrector in the half-unit direction. Multiplication
by two gives the unit direction required by (6.8). Its centered flux is
exactly the canonical centered flux multiplied by the coefficient scale.
The flux corrector here retains the literal raw heat-selection predicate;
transporting that predicate through the physical dilation remains separate.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The doubled half-direction meets the sphere condition of the flux inputs. -/
theorem euclideanNorm_two_smul_halfDirection {d : ℕ} (i : Fin d) :
    euclideanNorm ((2 : ℝ) • halfDirection i) = 1 := by
  have he : (2 : ℝ) • halfDirection i = unitVector i := by
    simp only [halfDirection, smul_smul]
    norm_num
  rw [he]
  simp [euclideanNorm, euclideanSq, dot, unitVector, Pi.single_apply, mul_ite]

/-- The source of the unit-direction raw heat selection is the canonical
centered flux with its exact deterministic coefficient factor. -/
theorem ae_unitAKMCenteredFlux_eq_scaled_canonicalCenteredFlux
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      centeredFlux (scaledAKMCorrector φ 2)
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
          ellipticityScale L •
            ((canonicalCorrectorFlux Q i (translate (r₀ • y) (reduce ω.1))).ofLp -
              (expectedCorrectorFlux Q i).ofLp) := by
  filter_upwards [ae_akmCenteredFlux_eq_scaled_canonicalCenteredFlux Q i φ hid]
    with ω hω
  filter_upwards [hω] with y hy
  rw [centeredFlux_scaledAKMCorrector, hy, smul_smul]
  congr 1
  ring

/-- The passed source estimate (6.8) supplies an actual heat-selected flux
corrector and all positive local gradient moments on the actual law. The
moment constant is chosen before the environment law and coordinate. -/
theorem exists_unitAKMFluxCorrector_with_canonical_source
    (h68 : FluxGradientEstimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (d : ℕ) [Fact (2 ≤ d)] (L r₀ p : ℝ) (hL : 1 ≤ L) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d),
      ∃ φ : Corrector (actualCoefficientLaw Q) (halfDirection i),
        ∃ S : FluxCorrector (scaledAKMCorrector φ 2),
          (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
            centeredFlux (scaledAKMCorrector φ 2)
              (project (r₀ := r₀) Q.ellipticity_parameter ω) y =
                ellipticityScale L •
                  ((canonicalCorrectorFlux Q i
                    (translate (r₀ • y) (reduce ω.1))).ofLp -
                      (expectedCorrectorFlux Q i).ofLp)) ∧
          ∀ j k : Fin d,
            (∫⁻ a, ENNReal.ofReal ((Real.sqrt
              (⨍ x in ball 0 1, euclideanSq (S.grad a j k x) ∂volume)) ^ p)
              ∂actualCoefficientLaw Q) ≤ ENNReal.ofReal C := by
  have hK : 1 < AKMUpperEllipticity L := by
    have hexp : 1 < Real.exp (2 * L) := Real.one_lt_exp_iff.mpr (by linarith)
    have hκ : 1 < ellipticityScale L := by
      unfold ellipticityScale
      nlinarith
    unfold AKMUpperEllipticity
    nlinarith
  obtain ⟨C, hC, hest⟩ := akm_flux_gradient_L2_moments h68 d
    (Fact.out : 2 ≤ d) (AKMUpperEllipticity L) p hK hp
  refine ⟨C, hC, ?_⟩
  intro Q i
  obtain ⟨φ, hid⟩ := exists_akmCorrector_global_gradient_identification hP Q i
  obtain ⟨hS, hb⟩ := hest (actualCoefficientLaw Q)
    (lawHypotheses_actualCoefficientLaw Q) ((2 : ℝ) • halfDirection i)
    (euclideanNorm_two_smul_halfDirection i) (scaledAKMCorrector φ 2)
  obtain ⟨S⟩ := hS
  exact ⟨φ, S, ae_unitAKMCenteredFlux_eq_scaled_canonicalCenteredFlux Q i φ hid, hb S⟩

end EinsteinRelation.Correctors

