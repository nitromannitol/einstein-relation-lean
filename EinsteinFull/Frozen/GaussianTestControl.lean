import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Exp

namespace EinsteinFull
open EinsteinRelation

/-- Exactly the scaled Gaussian bounds on a smooth test and its coordinate
partial derivatives. The k-th kernel derivative scaling is in the test itself.
No random field or stochastic estimate occurs in this predicate. -/
def HasGaussianTestControl {d : ℕ} (s : ℝ) (k : ℕ) (c : ℝ)
    (B : ℕ → ℝ) (ψ : SchwartzMap (Vec d) ℂ) : Prop :=
  ∀ (q : ℕ) (dirs : Fin q → Fin d) (x : Vec d),
    ‖iteratedFDeriv ℝ q (fun y => ψ y) x (fun j => unitVector (dirs j))‖ ≤
      B q * s ^ (-(d : ℝ) / 2 - ((q + k : ℕ) : ℝ) / 2) *
        Real.exp (-c * euclideanNorm x ^ 2 / s)

end EinsteinFull
