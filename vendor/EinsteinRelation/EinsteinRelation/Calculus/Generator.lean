import EinsteinRelation.Environment.Reduction
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring

/-! # Differential expressions for the two generators

These expressions are used classically at differentiability points. Distributional
equations for Lipschitz coefficients will use the associated weak formulation.
-/

open scoped BigOperators

namespace EinsteinRelation

/-- Coordinate derivative, computed using the Fréchet derivative. -/
noncomputable def coordinateDerivative {d : ℕ} (i : Fin d) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  fderiv ℝ f x (unitVector i)

/-- Spatial gradient in coordinates. -/
noncomputable def gradient {d : ℕ} (f : Vec d → ℝ) (x : Vec d) : Vec d :=
  fun i => coordinateDerivative i f x

/-- Spatial divergence of a vector field. -/
noncomputable def divergence {d : ℕ} (F : Vec d → Vec d) (x : Vec d) : ℝ :=
  ∑ i, coordinateDerivative i (fun y => F y i) x

/-- Row divergence of a matrix field. -/
noncomputable def rowDivergence {d : ℕ} (S : Vec d → Mat d) (x : Vec d) : Vec d :=
  fun j => ∑ k, coordinateDerivative k (fun y => S y j k) x

/-- Physical tilted generator, with force in coordinate `i`. -/
noncomputable def physicalGenerator {d : ℕ} (i : Fin d) (ω : FieldPair d)
    (lam : ℝ) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  (Real.exp (2 * ω.2 x) / 2) *
    divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x +
  lam * dot ((ω.1 x).mulVec (unitVector i)) (gradient f x)

/-- Reduced tilted generator. -/
noncomputable def reducedGenerator {d : ℕ} (i : Fin d) (ω : FieldPair d)
    (lam : ℝ) (f : Vec d → ℝ) (x : Vec d) : ℝ :=
  (1 / 2 : ℝ) *
    divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x +
  lam * dot ((reducedCoefficient ω x).mulVec (unitVector i)) (gradient f x)

theorem dot_smul_left {d : ℕ} (c : ℝ) (v w : Vec d) :
    dot (c • v) w = c * dot v w := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

/-- Multiplication by the clock density removes the physical speed measure. -/
theorem clockDensity_mul_physicalGenerator {d : ℕ} (i : Fin d) (ω : FieldPair d)
    (lam : ℝ) (f : Vec d → ℝ) (x : Vec d) :
    clockDensity ω x * physicalGenerator i ω lam f x = reducedGenerator i ω lam f x := by
  have hexp : clockDensity ω x * Real.exp (2 * ω.2 x) = 1 := by
    rw [clockDensity, ← Real.exp_add]
    simp
  have hforce : dot ((reducedCoefficient ω x).mulVec (unitVector i)) (gradient f x) =
      clockDensity ω x * dot ((ω.1 x).mulVec (unitVector i)) (gradient f x) := by
    rw [reducedCoefficient, Matrix.smul_mulVec, dot_smul_left]
  simp only [physicalGenerator, reducedGenerator, hforce]
  calc
    _ = (clockDensity ω x * Real.exp (2 * ω.2 x)) *
        divergence (fun y => (reducedCoefficient ω y).mulVec (gradient f y)) x / 2 +
        lam * (clockDensity ω x * dot ((ω.1 x).mulVec (unitVector i)) (gradient f x)) := by
      ring
    _ = _ := by rw [hexp]; ring

end EinsteinRelation
