import EinsteinRelation.Correctors.AKMRealizationFromGlobalGradient
import EinsteinRelation.Correctors.AKMCarrierIdentificationCellFluxAssembly

/-!
# Packaging the spatial corrector characterizations

Source: `paper/main.tex:693-702,727-729`. Scalar potentials are selected
from the proved almost-everywhere existence statement. Every corrector
field is retained; the cell integrability follows from the canonical
identification rather than being an additional premise.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- Package actual characterized potentials and gradients, retaining the
canonical identification needed for energy and flux transfer. -/
theorem exists_akmSpatialRealization_of_characterized_gradient
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (g : Coefficient d (AKMUpperEllipticity L) → Vec d → Vec d)
    (hg : Measurable (fun p : Coefficient d (AKMUpperEllipticity L) × Vec d => g p.1 p.2))
    (hid : ∀ᵐ ω ∂physicalReferenceLaw Q, ∀ᵐ y ∂(volume : Measure (Vec d)),
      (2 : ℝ) • (halfDirection i + g (project (r₀ := r₀) Q.ellipticity_parameter ω) y) =
        (correctorUnitVector i + (canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • y) (reduce ω.1))).ofLp)
    (hpot : ∀ᵐ a ∂actualCoefficientLaw Q, ∃ u : Vec d → ℝ,
      HasWeakGradient Set.univ u (g a) ∧
      (∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)) ∧
        MemLp (g a) 2 (volume.restrict (ball 0 R))) ∧
      Tendsto (fun R : ℝ => R⁻¹ * Real.sqrt (⨍ x in ball 0 R,
        (u x - ⨍ y in ball 0 R, u y ∂volume)^2 ∂volume)) atTop (𝓝 0))
    (hstationary : ∀ z : LatticeIndex d, ∀ᵐ a ∂actualCoefficientLaw Q,
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        g a (x + latticeShift z) = g (translateCoefficient (latticeShift z) a) x)
    (hharmonic : ∀ᵐ a ∂actualCoefficientLaw Q, HasWeakDivergence Set.univ
      (fun x => (a x).mulVec (halfDirection i + g a x)) (fun _ => 0)) :
    Nonempty (CanonicalAKMSpatialRealization Q i) := by
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  obtain ⟨u, hu⟩ := hpot.choice
  let φ : Corrector (actualCoefficientLaw Q) (halfDirection i) := {
    potential := u
    grad := g
    measurable_grad := hg
    weak_gradient := hu.mono fun _ h => h.1
    locally_square_integrable := hu.mono fun _ h => h.2.1
    stationary := hstationary
    harmonic := hharmonic
    sublinear := hu.mono fun _ h => h.2.2
    cell_integrable := akm_cellFlux_integrable_of_canonical_gradient Q i g hg hid }
  exact ⟨canonicalAKMSpatialRealization_of_global_gradient_identification Q i φ hid⟩

end EinsteinRelation.Correctors
