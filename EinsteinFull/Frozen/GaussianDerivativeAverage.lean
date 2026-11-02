import EinsteinFull.Frozen.GaussianAverage
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- Spatial derivatives of H_s are put on the kernel, with the kernel argument
-x fixing the integration-by-parts sign. No random-field derivative is assumed. -/
noncomputable def gaussianDerivativeAverage {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (s : ℝ) (hs : 0 < s)
    (k : ℕ) (dirs : Fin k → Fin d) (F : Lp ℂ 2 (reducedLaw Q)) :
    Lp ℂ 2 (reducedLaw Q) :=
  ∫ x : Vec d,
    iteratedFDeriv ℝ k (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0)
      (-x) (fun j => unitVector (dirs j)) •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x F

end EinsteinFull
