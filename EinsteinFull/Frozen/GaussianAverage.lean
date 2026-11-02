import EinsteinFull.Frozen.HomogenizedGaussianKernel
import EinsteinFull.Frozen.ComplexTranslation
import EinsteinFull.Frozen.ReducedLawStationary
import EinsteinFull.Frozen.ReducedLawProbability
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The paper's unforced spatial Gaussian average H_s, evaluated at the origin
as a genuine Bochner integral in complex L². -/
noncomputable def gaussianAverage {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s)
    (F : Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 2 (reducedLaw Q) :=
  ∫ x : Vec d, homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0 x •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F

end EinsteinFull
