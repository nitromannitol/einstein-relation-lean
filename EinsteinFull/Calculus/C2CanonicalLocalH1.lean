import EinsteinRelation.Correctors.AKMCenteredFluxTransfer
import EinsteinRelation.Correctors.AKMPotentialGradientTransfer
import EinsteinRelation.Correctors.SpatialBallLocalL2Support

/-!
# Physical local H¹ and centered flux of the same identified corrector

The concrete source corrector and its global gradient identification retain
the half-direction and range normalization. This conditional consumer provides
physical local H¹ and centered flux, without asserting producer or source-node closure.
-/

open MeasureTheory
noncomputable section
namespace EinsteinFull

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Environment.AKMTestIntegralSupport ReductionImageV3

/-- On the physical law, an identified raw corrector gives the literal
potential `2 r₀ φ(x/r₀)` and canonical gradient, locally in L² on every
Euclidean ball, with one common exceptional set. -/
theorem ae_canonicalCorrector_physical_localH1
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ᵐ ω ∂physicalReferenceLaw Q,
      HasWeakGradient Set.univ
        (fun x => (2 * r₀) * φ.potential
          (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x))
        (fun x => ((canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x (reduce ω.1))).ofLp) ∧
      ∀ (z : Vec d) (R : ℝ), 0 < R →
        MemLp (fun x => (2 * r₀) * φ.potential
          (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x))
          2 (volume.restrict (ball z R)) ∧
        MemLp (fun x => (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate x (reduce ω.1)))
          2 (volume.restrict (ball z R)) := by
  have hr : 0 < r₀ := zero_lt_one.trans_le Q.range_parameter
  have hw := ae_akmPotential_has_canonical_weakGradient Q i φ hid
  have hl := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae
    φ.locally_square_integrable
  filter_upwards [hw, hl, hid] with ω hweak hlocal hident
  refine ⟨hweak, ?_⟩
  have hu := memLp_two_on_euclidean_balls_dilation _
    (fun R hR => (hlocal R hR).1) r₀⁻¹ (2 * r₀) (inv_pos.mpr hr)
  have hg := memLp_two_on_euclidean_balls_dilation _
    (fun R hR => (hlocal R hR).2) r₀⁻¹ 2 (inv_pos.mpr hr)
  have hi := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (inv_ne_zero hr.ne')).ae hident
  have heq : (fun x => (2 : ℝ) • φ.grad
      (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)) =ᵐ[volume]
      (fun x => ((canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate x (reduce ω.1))).ofLp) := by
    filter_upwards [hi] with x hx
    rw [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] at hx
    ext j
    have hj := congrFun hx j
    simp only [Pi.smul_apply, Pi.add_apply, smul_eq_mul, PiLp.add_apply,
      halfDirection, correctorUnitVector, unitVector, Pi.single_apply] at hj ⊢
    split_ifs at hj ⊢ <;> linarith only [hj]
  intro z R hR
  constructor
  · simpa only [smul_eq_mul] using
      memLp_on_euclideanBall_of_origin_balls _ hu z R hR
  · have hcoord := (memLp_on_euclideanBall_of_origin_balls _ hg z R hR).ae_eq
      (ae_restrict_of_ae heq)
    let T := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
    exact T.toContinuousLinearMap.comp_memLp' hcoord

/-- The same identified source corrector supplies physical local H¹ and
centered flux on one physical full event. This is conditional support, not
a construction of the source corrector. -/
theorem ae_canonicalCorrector_physical_localH1_centeredFlux
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (φ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        (2 : ℝ) • (halfDirection i + φ.grad
          (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp) :
      (∀ᵐ ω ∂physicalReferenceLaw Q,
        HasWeakGradient Set.univ
          (fun x => (2 * r₀) * φ.potential
            (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x))
          (fun x => ((canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x (reduce ω.1))).ofLp) ∧
        (∀ (z : Vec d) (R : ℝ), 0 < R →
          MemLp (fun x => (2 * r₀) * φ.potential
            (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x))
            2 (volume.restrict (ball z R)) ∧
          MemLp (fun x => (canonicalCorrectorGradient Q i :
            Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
              (translate x (reduce ω.1)))
            2 (volume.restrict (ball z R))) ∧
        ∀ᵐ x ∂(volume : Measure (Vec d)),
          centeredFlux φ (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) =
            (ellipticityScale L / 2) •
              ((canonicalCorrectorFlux Q i (translate x (reduce ω.1))).ofLp -
                (expectedCorrectorFlux Q i).ofLp)) := by
  filter_upwards [ae_canonicalCorrector_physical_localH1 Q i φ hid,
    ae_akmCenteredFlux_physical_coordinate Q i φ hid] with ω hlocal hflux
  exact ⟨hlocal.1, hlocal.2, hflux⟩

end EinsteinFull
