import EinsteinRelation.Environment.Smooth
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull

open EinsteinRelation

/-- Assumption 1.2: smooth fields with a common bound for the sum of the
Euclidean operator norms of their derivatives, at every positive order. -/
def IsSmoothWithBounds {d : ℕ} (Λ : ℕ → ℝ) (ω : FieldPair d) : Prop :=
  IsSmoothFieldPair ω ∧ ∀ k : ℕ, 1 ≤ k →
    ∃ A B : ℝ, 0 ≤ A ∧ 0 ≤ B ∧ A + B ≤ Λ k ∧
      (∀ (x : Vec d) (v : Fin k → Vec d) (ξ : Vec d),
        euclideanNorm (Matrix.mulVec (fun i j => iteratedFDeriv ℝ k (fun y => ω.1 y i j) x v) ξ) ≤
          A * (∏ j, euclideanNorm (v j)) * euclideanNorm ξ) ∧
      (∀ (x : Vec d) (v : Fin k → Vec d),
        |iteratedFDeriv ℝ k (fun y => ω.2 y) x v| ≤
          B * ∏ j, euclideanNorm (v j))

end EinsteinFull
