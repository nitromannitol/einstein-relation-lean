import EinsteinRelation.Correctors.PairedPDEWeakCaccioppoli
import EinsteinRelation.Correctors.PairedParabolicEquation

/-! # Weak energy comparison for locally agreeing environments

Source: `paper/main.tex:817–840`. The actual homogeneous difference
equation supplies Caccioppoli for the paired scalar field and its actual
gradient difference, without independence or smoothness assumptions.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Local agreement of the two coefficient fields gives the paired weak
cutoff estimate. The homogeneous paired equation is derived internally.
Source: `paper/main.tex:817–840`. -/
theorem paired_cutoff_energy {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A₁ A₂ : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U) (hA : Set.EqOn A₁ A₂ U)
    {u₁ u₂ : ℝ × Vec d → ℝ} {G₁ G₂ : ℝ × Vec d → Vec d}
    (h₁ : IsParabolicSolution A₁ I U u₁ G₁)
    (h₂ : IsParabolicSolution A₂ I U u₂ G₂)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U) :
    (∫ z in I ×ˢ U, ζ z ^ 2 * euclideanSq (G₁ z - G₂ z)) ≤
      2 * (∫ z in I ×ˢ U, (u₁ z - u₂ z)^2 * ζ z * fderiv ℝ ζ z (1, 0)) +
        4 * K^2 * ∫ z in I ×ˢ U, (u₁ z - u₂ z)^2 *
          euclideanSq (fun j => fderiv ℝ ζ z (0, unitVector j)) :=
  (parabolicSolution_cutoff_energy hK hI hU
    (paired_parabolicSolution hK hI hU.measurableSet hA h₁ h₂) hζ hζc hζsupp).2.2

end EinsteinRelation.Correctors
