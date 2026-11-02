import EinsteinFull.Frozen.HomogeneousAverage
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open MeasureTheory

namespace EinsteinFull
open EinsteinRelation

/-- Derivatives of the homogeneous semigroup fall on the backward kernel at -x,
so no derivatives of the stationary observation are selected. -/
noncomputable def homogeneousDerivativeAverage {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ)
    (k : ℕ) (dirs : Fin k → Fin d) (F : Lp ℂ 2 (reducedLaw Q)) :
    Lp ℂ 2 (reducedLaw Q) :=
  ∫ x : Vec d,
    iteratedFDeriv ℝ k (homogenizedGaussianKernel Q i s hs (-ζ))
      (-x) (fun j => unitVector (dirs j)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F

end EinsteinFull
