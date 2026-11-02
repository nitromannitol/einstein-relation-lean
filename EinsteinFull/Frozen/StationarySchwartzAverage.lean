import EinsteinFull.Frozen.ComplexTranslation
import EinsteinFull.Frozen.ReducedLawStationary
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- The literal stationary convolution with an actual Schwartz test.
Its kernel is evaluated at -x to fix the usual convolution convention. -/
noncomputable def stationarySchwartzAverage {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (ψ : SchwartzMap (Vec d) ℂ)
    (F : Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 2 (reducedLaw Q) :=
  ∫ x : Vec d, ψ (-x) •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F

end EinsteinFull
