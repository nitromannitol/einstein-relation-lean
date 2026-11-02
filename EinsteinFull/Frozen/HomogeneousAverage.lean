import EinsteinFull.Frozen.HomogenizedGaussianKernel
import EinsteinFull.Frozen.ComplexTranslation
import EinsteinFull.Frozen.ReducedLawStationary
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace EinsteinFull
open EinsteinRelation

/-- The actual homogeneous complex-force semigroup, applied spatially at the
origin. Its drift is zeta A e_i and the forward transition kernel
is integrated against translated observations. -/
noncomputable def homogeneousAverage {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (ζ : ℂ) (F : Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 2 (reducedLaw Q) :=
  ∫ x : Vec d, homogenizedGaussianKernel Q i s hs ζ x •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F

end EinsteinFull
