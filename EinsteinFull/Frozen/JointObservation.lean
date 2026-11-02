import EinsteinFull.Frozen.CommutatorObservation
import EinsteinFull.Frozen.JointObservationIndex
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- Given complex L² classes represent precisely the REAL joint field (Xi,mu-E mu).
The two summand indices identify d²+1 coordinates without an arbitrary ordering. -/
def IsJointObservation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)) : Prop :=
  (∀ j i : Fin d, (Z (.inl (j,i)) : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
    fun ω => (commutatorObservation Q j i ω : ℂ)) ∧
  (Z (.inr ()) : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
    fun ω => ((ω.2 0 - ∫ ω', ω'.2 0 ∂reducedLaw Q : ℝ) : ℂ)

end EinsteinFull
