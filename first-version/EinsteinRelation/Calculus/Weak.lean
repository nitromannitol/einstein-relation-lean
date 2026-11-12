import EinsteinRelation.Calculus.Generator
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi

/-! # Spatial weak equations

All equations are tested against actual smooth functions with compact support.
The reference measure is coordinate Lebesgue measure on `Fin d → ℝ`; geometric
balls are expressed using the Euclidean norm defined in the environment module.
-/

open MeasureTheory

namespace EinsteinRelation

/-- A smooth compactly supported scalar test in the specified open domain. -/
def IsSpatialTest {d : ℕ} (U : Set (Vec d)) (φ : Vec d → ℝ) : Prop :=
  ContDiff ℝ (⊤ : ℕ∞) φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ U

/-- A locally integrable weak coordinate derivative. -/
def HasWeakPartialDerivative {d : ℕ} (U : Set (Vec d)) (i : Fin d)
    (f g : Vec d → ℝ) : Prop :=
  LocallyIntegrableOn f U volume ∧ LocallyIntegrableOn g U volume ∧
  ∀ φ : Vec d → ℝ, IsSpatialTest U φ →
    (∫ x in U, f x * coordinateDerivative i φ x) = -(∫ x in U, g x * φ x)

/-- A weak spatial gradient, with its individual coordinates locally integrable. -/
def HasWeakGradient {d : ℕ} (U : Set (Vec d))
    (f : Vec d → ℝ) (g : Vec d → Vec d) : Prop :=
  ∀ i : Fin d, HasWeakPartialDerivative U i f (fun x => g x i)

/-- The weak divergence `div F = h`, with local integrability made explicit. -/
def HasWeakDivergence {d : ℕ} (U : Set (Vec d))
    (F : Vec d → Vec d) (h : Vec d → ℝ) : Prop :=
  (∀ i : Fin d, LocallyIntegrableOn (fun x => F x i) U volume) ∧
  LocallyIntegrableOn h U volume ∧
  ∀ φ : Vec d → ℝ, IsSpatialTest U φ →
    (∫ x in U, dot (F x) (gradient φ x)) = -(∫ x in U, h x * φ x)

/-- Weak row divergence of a matrix field, in the manuscript convention. -/
def HasWeakRowDivergence {d : ℕ} (U : Set (Vec d))
    (S : Vec d → Mat d) (g : Vec d → Vec d) : Prop :=
  ∀ j : Fin d, HasWeakDivergence U (fun x k => S x j k) (fun x => g x j)

theorem hasWeakDivergence_zero {d : ℕ} (U : Set (Vec d)) :
    HasWeakDivergence U (fun _ => 0) (fun _ => 0) := by
  refine ⟨fun _ => ?_, ?_, ?_⟩
  · exact locallyIntegrableOn_zero
  · exact locallyIntegrableOn_zero
  · intro φ _
    simp [dot]

end EinsteinRelation
