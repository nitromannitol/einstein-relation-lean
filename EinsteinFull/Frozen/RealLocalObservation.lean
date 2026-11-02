import EinsteinFull.Frozen.ReducedLaw
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- A real observation of the joint reduced fields in the Euclidean ball
of the supplied radius, represented in complex L². -/
def IsRealLocalObservation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ)
    (F : Lp ℂ 2 (reducedLaw Q)) : Prop :=
  ∃ f : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < R}] f ∧
    (fun ω => (f ω : ℂ)) =ᵐ[reducedLaw Q] (F : FieldPair d → ℂ)

end EinsteinFull
