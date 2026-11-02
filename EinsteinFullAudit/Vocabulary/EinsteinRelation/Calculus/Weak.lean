import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction

/-! Vocabulary for `EinsteinRelation.Calculus.Weak`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

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

end EinsteinRelation
