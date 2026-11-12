import EinsteinRelation.Correctors.AKMLocalCanonicalIdentificationMeanFlux

/-! # The source unit-cell convention for the AKM local corrector

Source: `paper/main.tex:948-955`; AKM (4.126), p. 173. The coordinate
expectations over `[0,1]^d` agree with the repository canonical flux, with
the normalization for the half-direction retained explicitly.
-/
open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The literal coordinate formula used by `firstOrderMeanFlux` has the
canonical value on the actual coefficient law. -/
theorem akmLocal_meanFlux_sourceCell_of_canonical_gradient
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (g : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g p.1 p.2))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) :
    (fun j => ∫ a, ∫ x in Set.Icc (0 : Vec d) 1,
      ((a x).mulVec (halfDirection i + g a x)) j ∂volume ∂actualCoefficientLaw Q) =
      (ellipticityScale L / 2) • (expectedCorrectorFlux Q i).ofLp := by
  have hvol : volume (Set.Icc (0 : Vec d) 1) = 1 := by
    simp [Real.volume_Icc_pi]
  letI : IsFiniteMeasure (volume.restrict (Set.Icc (0 : Vec d) 1)) :=
    ⟨by simp [hvol]⟩
  funext j
  have h := (akmLocal_meanFlux_coordinate_of_canonical_gradient Q i j g hg hid
    (Set.Icc (0 : Vec d) 1)).2
  simpa only [hvol, ENNReal.toReal_one, one_mul, Pi.smul_apply, smul_eq_mul] using h

end EinsteinRelation.Correctors
