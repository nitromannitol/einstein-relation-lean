import Mathlib.Analysis.Calculus.FDeriv.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Reduction

/-! Restated from the library module `EinsteinRelation.Calculus.Generator`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

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
end EinsteinRelation
