import EinsteinFull.Frozen.ProfileTaylorCoefficient
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull

/-- The literal finite part `M_d(H)` in equation `e:finite-part`, with the subtraction convention
of the manuscript; the Gaussian exponent is positive. -/
noncomputable def profileFinitePart (d : ℕ) (u₀ u₂ γ : ℝ) (_hγ : 0 < γ) : ℝ :=
  (∫ u in Set.Ioo (0 : ℝ) 1,
    (gaussianProfile u₀ u₂ γ u -
      ∑ j : Fin (d + 1), profileTaylorCoefficient u₀ u₂ γ j.val * u ^ j.val) /
        u ^ (d + 1)) +
  (∫ u in Set.Ioi (1 : ℝ), gaussianProfile u₀ u₂ γ u / u ^ (d + 1)) -
  ∑ j : Fin d, profileTaylorCoefficient u₀ u₂ γ j.val / ((d - j.val : ℕ) : ℝ)

end EinsteinFull
