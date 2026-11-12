import EinsteinRelation.Correctors.HomogenizedMatrixBounds
import EinsteinRelation.Correctors.AKMFluxIdentification
import EinsteinRelation.Correctors.GTRegularCoefficientSupport

/-! Source: `paper/main.tex:733-745`. The bounded canonical affine
gradient controls the literal centered flux in the Poisson equation. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- The expected canonical flux is the corresponding homogenized column. -/
theorem expectedCorrectorFlux_euclideanNorm_le {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    euclideanNorm (expectedCorrectorFlux Q i).ofLp ≤ sourceReducedBound L := by
  convert homogenizedMatrix_euclideanNorm_mulVec_unitVector_le Q i using 1
  congr 1
  ext j
  simp [Matrix.mulVec, dotProduct, unitVector, homogenizedMatrix, Pi.single_apply]

/-- On one event, any local bound on the actual affine corrector gradient
gives the needed local bound on its centered flux. The set, center and
bound may all be chosen after the environment. -/
theorem ae_canonicalCenteredFlux_bound_of_affineBound {d : ℕ} {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ρ ∂reducedEnvironmentLaw Q, ∀ (U : Set (Vec d)) (A : ℝ),
      (∀ᵐ x ∂volume.restrict U,
        euclideanNorm ((correctorUnitVector i +
          (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x ρ)).ofLp) ≤ A) →
      ∀ᵐ x ∂volume.restrict U,
        euclideanNorm ((canonicalCorrectorFlux Q i (translate x ρ) -
          expectedCorrectorFlux Q i).ofLp) ≤ sourceReducedBound L * (A + 1) := by
  have hsp := ae_spatial_canonicalCorrectorFlux Q i (σ := id) measurable_id
  filter_upwards [hsp, ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q]
    with ρ hρ himage
  obtain ⟨η, hη, hηρ⟩ := himage
  have ha : IsElliptic (sourceReducedBound L) ρ.1 := by
    rw [← hηρ]
    exact (sourceReducedBound_support Q.ellipticity_parameter hη).2.1
  have hK : 0 < sourceReducedBound L := zero_lt_one.trans_le
    (sourceReducedBound_support Q.ellipticity_parameter hη).1
  intro U A hA
  filter_upwards [ae_restrict_of_ae hρ, hA] with x hx hxA
  simp only [id_eq] at hx
  have hnorm : euclideanNorm (-(expectedCorrectorFlux Q i).ofLp) =
      euclideanNorm (expectedCorrectorFlux Q i).ofLp := by
    rw [TimeChange.euclideanNorm_eq_norm_toLp, TimeChange.euclideanNorm_eq_norm_toLp]
    simp
  calc
    _ = euclideanNorm ((canonicalCorrectorFlux Q i (translate x ρ)).ofLp +
        -(expectedCorrectorFlux Q i).ofLp) := by rfl
    _ ≤ euclideanNorm (canonicalCorrectorFlux Q i (translate x ρ)).ofLp +
        euclideanNorm (-(expectedCorrectorFlux Q i).ofLp) :=
      TimeChange.euclideanNorm_add_le _ _
    _ ≤ sourceReducedBound L * A + sourceReducedBound L := by
      rw [hnorm, hx]
      exact add_le_add ((isElliptic_mulVec_euclideanNorm_le hK ha x _).trans
        (mul_le_mul_of_nonneg_left hxA hK.le))
        (expectedCorrectorFlux_euclideanNorm_le Q i)
    _ = _ := by ring

end EinsteinRelation.Correctors
