import EinsteinFull.Frozen.ReducedLaw
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- Complex local class measurable with respect to the joint reduced fields
inside the actual Euclidean ball. No approximation or bound is an input. -/
def IsComplexLocalObservation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (F : Lp ℂ 2 (reducedLaw Q)) : Prop :=
  ∃ f : FieldPair d → ℂ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < R}] f ∧
    f =ᵐ[reducedLaw Q] (F : FieldPair d → ℂ)

end EinsteinFull
