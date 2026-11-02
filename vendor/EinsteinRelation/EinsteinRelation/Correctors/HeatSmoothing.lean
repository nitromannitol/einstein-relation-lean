import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Euclidean heat smoothing of environment fields

The Euclidean heat kernel and the smoothed field `H_t f` used to state the scalar averaging
hypothesis of the two-scale decomposition (`paper/main.tex:961`).
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors

/-- The Euclidean heat kernel of `e^{tΔ}` at time `t > 0`, `(4πt)^{-d/2} exp(-|x|²/(4t))`
(`paper/main.tex:961`, convolution with the Euclidean heat kernel at time `t`). -/
def euclideanHeatKernel {d : ℕ} (t : ℝ) (x : Vec d) : ℝ :=
  (4 * Real.pi * t) ^ (-(d : ℝ) / 2) * Real.exp (-(euclideanSq x) / (4 * t))

/-- The smoothed field `H_t f` evaluated at the origin of the environment (`paper/main.tex:961`):
`H_0` is the identity and, for `t > 0`, `H_t f(ω) = ∫ p_t(z) f(T_z ω) dz`, where `p_t` is the
Euclidean heat kernel. For a stationary field the value at `x` is the same integral at `T_x ω`. -/
def heatSmoothed {d : ℕ} (t : ℝ) (f : FieldPair d → ℝ) (ω : FieldPair d) : ℝ :=
  if t = 0 then f ω else
    ∫ z : Vec d, euclideanHeatKernel t z * f (translate z ω) ∂(volume : Measure (Vec d))

end EinsteinRelation.Correctors

end
