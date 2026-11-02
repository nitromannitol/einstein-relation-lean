import EinsteinFull.Frozen.ReducedLaw
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.Complex.Basic

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- A bounded real local observable, represented in complex `L²` of the
reduced law. Locality uses the joint coefficient--clock restriction. -/
def IsBoundedLocalObservation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (F : Lp ℂ 2 (reducedLaw Q)) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∃ f : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < R}] f ∧
    (fun ω => (f ω : ℂ)) =ᵐ[reducedLaw Q] (F : FieldPair d → ℂ) ∧
    ∃ M : ℝ, ∀ ω, |f ω| ≤ M

end EinsteinFull
