import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic

/-! Vocabulary for `EinsteinRelation.Environment.Smooth`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinRelation

/-- The physical matrix entries and potential are smooth on all of space. -/
def IsSmoothFieldPair {d : ℕ} (ω : FieldPair d) : Prop :=
  (∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.1 x j k)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.2 x)

end EinsteinRelation
