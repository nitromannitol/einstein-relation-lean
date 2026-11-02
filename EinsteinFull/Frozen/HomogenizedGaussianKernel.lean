import EinsteinFull.Frozen.HomogenizedCoefficient
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt

namespace EinsteinFull

open EinsteinRelation

/-- The Gaussian kernel of (1/2) A:D² + zeta (A e_i).D, with its
bilinear entire continuation in the force. A is the actual homogenized matrix. -/
noncomputable def homogenizedGaussianKernel {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (_hs : 0 < s)
    (ζ : ℂ) (x : Vec d) : ℂ :=
  let A := homogenizedCoefficient Q
  let v := A.mulVec (unitVector i)
  let w : Fin d → ℂ := fun j => (x j : ℂ) - ζ * (s : ℂ) * (v j : ℂ)
  (((2 * Real.pi * s) ^ (-(d : ℝ) / 2) / Real.sqrt A.det : ℝ) : ℂ) *
    Complex.exp (-(∑ j : Fin d, ∑ k : Fin d,
      w j * ((A⁻¹) j k : ℂ) * w k) / (2 * (s : ℂ)))

end EinsteinFull
