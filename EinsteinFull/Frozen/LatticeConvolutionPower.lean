import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Basic.Real.Basic

namespace EinsteinFull

/-- Lattice convolution powers, with the zeroth power the unit mass at zero. -/
def latticeConvolutionPower (p : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, n => if n = 0 then 1 else 0
  | j + 1, n => ∑ k ∈ Finset.range (n + 1), p k * latticeConvolutionPower p j (n - k)

end EinsteinFull
