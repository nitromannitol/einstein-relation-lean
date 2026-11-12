import EinsteinRelation.Correctors.ParabolicFluxRegularizedEnergy
import EinsteinRelation.Correctors.ParabolicEnergyCutoff

open MeasureTheory Filter Metric
open scoped Topology ENNReal Convolution
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Testing the actual weak equation by the square of a compact cutoff
and the solution gives the local energy identity. No smoothness or temporal
derivative of the solution, nor an energy identity, is assumed.
Source: `paper/main.tex:832–840`. -/
theorem parabolicFlux_energy_identity {d : ℕ} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    {J : ℝ × Vec d → Vec d}
    (hu : MemLp u 2 (volume.restrict (I ×ˢ U)))
    (hG : ∀ j, MemLp (fun z => G z j) 2 (volume.restrict (I ×ˢ U)))
    (hw : ∀ᵐ t ∂volume.restrict I,
      HasWeakGradient U (fun x => u (t,x)) (fun x => G (t,x)))
    (hflux : ∀ j, MemLp (fun z => J z j) 2 (volume.restrict (I ×ˢ U)))
    (hweak : ∀ ψ : ℝ × Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ →
      HasCompactSupport ψ → tsupport ψ ⊆ interior I ×ˢ U →
      (∫ z in I ×ˢ U, -(u z) * fderiv ℝ ψ z (1,0) +
        dot (J z) (fun j => fderiv ℝ ψ z (0,unitVector j))) = 0)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U)
 :
    Integrable (fun z => dot (J z)
      (fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0, unitVector j)))
      (volume.restrict (I ×ˢ U)) ∧
      (∫ z in I ×ˢ U, dot (J z)
        (fun j => ζ z ^ 2 * G z j + 2 * ζ z * u z * fderiv ℝ ζ z (0, unitVector j))) =
        ∫ z in I ×ˢ U, (u z)^2 * ζ z * fderiv ℝ ζ z (1, 0) := by
  apply parabolicFlux_cutoff_energy_identity hu hflux hweak hζ hζc hζsupp
  exact parabolicEnergy_cutoff_data hI hU hu hG hw hζ hζc
    (hζsupp.trans (Set.prod_mono interior_subset Set.Subset.rfl))

end EinsteinRelation.Correctors
