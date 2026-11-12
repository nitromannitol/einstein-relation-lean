import EinsteinRelation.Correctors.AffineGradientAllCenters
import EinsteinRelation.Correctors.AKMPhysicalScalarSobolev
import EinsteinRelation.Correctors.GTFourBallCoefficientSupport
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger
open Environment.AKMTestIntegralSupport ReductionImageV3
/-- Source: `paper/main.tex:727-735`. The canonical affine gradient is
controlled on every unit ball by the actual physical scalar oscillation. -/
theorem ae_physicalAKMAffineGradient_local_bound_of_GT
    (h817 : LocalBoundednessEstimate) (h832 : InteriorGradientEstimate)
    (h836 : InteriorRegularRepresentative)
    (d : ℕ) [Fact (2 ≤ d)] (L : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (φ : Corrector (actualCoefficientLaw Q) (halfDirection i)),
      (∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        (2 : ℝ) • (halfDirection i + φ.grad
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) →
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ (z : Vec d) (c : ℝ),
        ∀ᵐ x ∂volume.restrict (ball z 1),
          euclideanNorm ((correctorUnitVector i + (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x (reduce ω.1))).ofLp) ≤ C * (1 + Real.sqrt
                (∫ x in ball z 4, |(2 * r₀) * φ.potential
                  (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) - c| ^ 2
                  ∂volume)) := by
  have hB : 0 < sourceReducedBound L := by unfold sourceReducedBound; positivity
  have hΛ : 0 < ((d : ℝ) + 1) * sourceReducedBound L := by positivity
  have hK : 0 < sourceReducedBound L + 3 * (Real.exp (2 * L) * (L + 2 * L ^ 2)) := by
    have : 0 ≤ L := zero_le_one.trans hL
    positivity
  obtain ⟨C, hC, hlocal⟩ := scalar_corrector_affine_local_gradient_bound_at_center_of_GT
    h817 h832 h836 d (Fact.out : 2 ≤ d) (sourceReducedBound L)⁻¹
    (((d : ℝ) + 1) * sourceReducedBound L)
    (sourceReducedBound L + 3 * (Real.exp (2 * L) * (L + 2 * L ^ 2)))
    (1 / 2) (inv_pos.mpr hB) hΛ hK (by norm_num) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro r₀ Q i φ hid
  have hc := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (reduced_gt_coefficient_hypotheses_ball_four Q)
  filter_upwards [hc, ae_physicalAKMPotential_affine_weakSolution Q i φ hid] with ω hcoeff hw
  intro z c
  convert hlocal z (reduce ω.1).1 (hcoeff z).1 (hcoeff z).2
    (fun x => (2 * r₀) * φ.potential
      (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x))
    (fun x => ((canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
        (translate x (reduce ω.1))).ofLp)
    i c (hw z 4 (by norm_num) c).1 (hw z 4 (by norm_num) c).2 using 1
