import EinsteinRelation.Correctors.AKMPotentialGradientTransfer
import EinsteinRelation.Correctors.AKMStationaryCellMoments
import EinsteinRelation.Correctors.NormalizedScalarCorrectorUniqueness
import EinsteinRelation.Correctors.NormalizedScalarPhysicalLawTransportSupport

/-!
# Comparing the production scalar predicate with the raw AKM potential

Source: `paper/main.tex:699-708,722,735-737`. Equal weak gradients imply
that the potentials differ by a spatial constant. This proves the gauge
comparison for the production scalar-corrector meaning, without assuming a
potential identification or uniqueness input.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3
open NormalizedScalarPhysicalLawTransportSupport
open NormalizedSpatialRepresentativeSupport
open NormalizedScalarCorrectorUniqueness

/-- The canonical scalar corrector is the rescaled AKM potential modulo a
spatial constant, for every representative in the production source predicate. -/
theorem akmPotential_gauge_identification_production
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ψ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + ψ.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp) :
      ∀ (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
        (φ : FieldPair d → Point d → ℝ),
        IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
        ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ c : ℝ,
          (fun x : Vec d => φ (reduce ω.1) (WithLp.toLp 2 x)) =ᵐ[volume]
            (fun x => (2 * r₀) * ψ.potential
              (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) + c) := by
  intro ζ R hR y φ hφ
  have hw := ae_akmPotential_has_canonical_weakGradient Q i ψ hid
  have hφw := (measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae hφ.2
  have hd : 0 < d := by have := (Fact.out : 2 ≤ d); omega
  filter_upwards [hφw, hw] with ω hω hψ
  obtain ⟨_, hφ, _⟩ := hω
  have hloc : LocallyIntegrable
      (fun x : Vec d => φ (reduce ω.1) (WithLp.toLp 2 x) -
        (2 * r₀) * ψ.potential
          (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x)) volume :=
    (locallyIntegrableOn_univ.mp (hφ ⟨0, hd⟩).1).sub
      (locallyIntegrableOn_univ.mp (hψ ⟨0, hd⟩).1)
  obtain ⟨c, hc⟩ := ae_eq_const_of_zero_weak_gradient hloc
    (fun j η hη => integral_sub_mul_coordinateDerivative_eq_zero hφ hψ j hη)
  refine ⟨c, ?_⟩
  filter_upwards [hc] with x hx
  change φ (reduce ω.1) (WithLp.toLp 2 x) - _ = c at hx
  linarith

/-- Changing to a source representative with the same spatial gradient
preserves the physical gauge comparison. -/
theorem akmPotential_gauge_identification_of_ae_grad_production
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ψ φ₀ : Corrector (actualCoefficientLaw Q) (halfDirection i))
    (heq : ∀ᵐ a ∂actualCoefficientLaw Q, ψ.grad a =ᵐ[volume] φ₀.grad a)
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + φ₀.grad
        (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
      (correctorUnitVector i + (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • y) (reduce ω.1))).ofLp) :
    ∀ (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
      (φ : FieldPair d → Point d → ℝ),
      IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ c : ℝ,
        (fun x : Vec d => φ (reduce ω.1) (WithLp.toLp 2 x)) =ᵐ[volume]
          (fun x => (2 * r₀) * ψ.potential
            (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) + c) := by
  apply akmPotential_gauge_identification_production Q i ψ
  have heq' := (measurePreserving_akmProject Q).quasiMeasurePreserving.ae heq
  filter_upwards [heq', hid] with ω hω hiω
  filter_upwards [hω, hiω] with y hy hiy
  simpa only [hy] using hiy

/-- An actual source-carrier corrector supplies the gauge comparison for
all production normalized scalar representatives simultaneously. -/
theorem exists_akmCorrector_gauge_identification_production
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ ψ : Corrector (actualCoefficientLaw Q) (halfDirection i),
      ∀ (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
        (φ : FieldPair d → Point d → ℝ),
        IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
        ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ c : ℝ,
          (fun x : Vec d => φ (reduce ω.1) (WithLp.toLp 2 x)) =ᵐ[volume]
            (fun x => (2 * r₀) * ψ.potential
              (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) + c) := by
  obtain ⟨ψ, hid⟩ := exists_akmCorrector_global_gradient_identification hP Q i
  exact ⟨ψ, akmPotential_gauge_identification_production Q i ψ hid⟩

/-- The stationary AKM representative has finite cell moments and agrees,
modulo the physical constant gauge, with every production scalar representative.
All constants precede the environment law and the direction. -/
theorem exists_stationary_akmScalar_production_cell_moments
    (h45 : ScalarStationaryEstimate)
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    (d : ℕ) [Fact (2 ≤ d)] (hd : 2 < d) (L r₀ p : ℝ)
    (hL : 1 ≤ L) (hp : 0 < p) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d),
      ∃ ψ : Corrector (actualCoefficientLaw Q) (halfDirection i),
        Measurable (fun q : Coefficient d (AKMUpperEllipticity L) × Vec d =>
          ψ.potential q.1 q.2) ∧
        ScalarStationary (actualCoefficientLaw Q) ψ.potential ∧
        (∫ a, ⨍ x in unitCell d, ψ.potential a x ∂volume
          ∂actualCoefficientLaw Q) = 0 ∧
        (∫⁻ a, ENNReal.ofReal ((Real.sqrt
          (⨍ x in unitCell d, |ψ.potential a x| ^ 2 ∂volume)) ^ p)
          ∂actualCoefficientLaw Q) ≤ ENNReal.ofReal C ∧
        ∀ (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
          (φ : FieldPair d → Point d → ℝ),
          IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ →
          ∀ᵐ ω ∂physicalReferenceLaw Q, ∃ c : ℝ,
            (fun x : Vec d => φ (reduce ω.1) (WithLp.toLp 2 x)) =ᵐ[volume]
              (fun x => (2 * r₀) * ψ.potential
                (project (r₀ := r₀) Q.ellipticity_parameter ω) (r₀⁻¹ • x) + c) := by
  have hK : 1 < AKMUpperEllipticity L := by
    have hexp : 1 < Real.exp (2 * L) := Real.one_lt_exp_iff.mpr (by linarith)
    have hκ : 1 < ellipticityScale L := by
      unfold ellipticityScale
      nlinarith
    unfold AKMUpperEllipticity
    nlinarith
  obtain ⟨C, hC, hest⟩ := akm_stationary_scalar_cell_moments h45 d hd
    (AKMUpperEllipticity L) p hK hp
  refine ⟨C, hC, ?_⟩
  intro Q i
  obtain ⟨φ₀, hid⟩ := exists_akmCorrector_global_gradient_identification hP Q i
  obtain ⟨ψ, hm, hg, hs, hz, hb⟩ := hest (actualCoefficientLaw Q)
    (lawHypotheses_actualCoefficientLaw Q) (halfDirection i) (halfDirection_mem_ball i) φ₀
  exact ⟨ψ, hm, hs, hz, hb,
    akmPotential_gauge_identification_of_ae_grad_production Q i ψ φ₀ hg hid⟩

end EinsteinRelation.Correctors

