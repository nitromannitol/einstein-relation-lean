import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Matrix.Mul
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction

/-! Vocabulary for `EinsteinRelation.Environment.SourceReducedBoundSupport`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinRelation

/-- A concrete value of the reduced-field bound `Λ(L)` in
`paper/main.tex`, equation `eq.reduced-bounds`, depending only on the original
coefficient and potential bound `L`. -/
noncomputable def sourceReducedBound (L : ℝ) : ℝ :=
  Real.exp (2 * L) * (3 * L^2 + L + 1)

end EinsteinRelation
