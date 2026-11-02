import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic

/-! Vocabulary for `EinsteinRelation.Environment.Reduction`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinRelation

/-- Clock density `μ = exp(-2V)`. -/
noncomputable def clockDensity {d : ℕ} (ω : FieldPair d) (x : Vec d) : ℝ :=
  Real.exp (-2 * ω.2 x)

/-- Divergence-form coefficient `a = exp(-2V) a₀`. -/
noncomputable def reducedCoefficient {d : ℕ} (ω : FieldPair d) (x : Vec d) : Mat d :=
  clockDensity ω x • ω.1 x

/-- The continuous reduced coefficient pair. -/
noncomputable def reduce {d : ℕ} (ω : FieldPair d) : FieldPair d :=
  (⟨reducedCoefficient ω,
    (Real.continuous_exp.comp (continuous_const.mul ω.2.continuous)).smul ω.1.continuous⟩,
   ⟨clockDensity ω, Real.continuous_exp.comp (continuous_const.mul ω.2.continuous)⟩)

end EinsteinRelation
