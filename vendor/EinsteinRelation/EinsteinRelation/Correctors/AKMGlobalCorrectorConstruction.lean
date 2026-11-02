import EinsteinRelation.Correctors.AKMCorrectorConstruction

/-!
# A global identification of the actual AKM scalar corrector

Source: `paper/main.tex:693-702,716,727-729`. This retains the global
spatial gradient identity when packaging the raw corrector. It is needed
to compare potentials on arbitrary balls, rather than only on the unit ball.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The raw scalar corrector exists with its gradient identified on all of
space, with the physical range and the half-direction factors explicit. -/
theorem exists_akmCorrector_global_gradient_identification
    (hP : External.GilbargTrudinger.BallPoincareEstimate)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ φ : Corrector (actualCoefficientLaw Q) (halfDirection i),
      ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
        (2 : ℝ) • (halfDirection i +
          φ.grad (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp := by
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  obtain ⟨g, hg, hid, hpot⟩ := exists_akm_sublinear_characterized_gradient hP Q i
  obtain ⟨u, hu⟩ := hpot.choice
  let φ : Corrector (actualCoefficientLaw Q) (halfDirection i) := {
    potential := u
    grad := g
    measurable_grad := hg
    weak_gradient := hu.mono fun _ h => h.1
    locally_square_integrable := hu.mono fun _ h => h.2.1
    stationary := fun z =>
      ae_akm_stationary_of_canonical_gradient Q i g hg hid (latticeShift z)
    harmonic := ae_akm_harmonic_of_canonical_gradient Q i g hg hid
    sublinear := hu.mono fun _ h => h.2.2
    cell_integrable := akm_cellFlux_integrable_of_canonical_gradient Q i g hg hid }
  exact ⟨φ, hid⟩

end EinsteinRelation.Correctors
