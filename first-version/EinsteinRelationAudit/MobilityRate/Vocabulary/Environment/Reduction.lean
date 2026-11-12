import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import EinsteinRelationAudit.MobilityRate.Vocabulary.Environment.Basic

/-! Restated from the library module `EinsteinRelation.Environment.Reduction`:
the declarations of that module that the statement of
`EinsteinRelationAudit.MobilityRate.mobility_rate` depends on, in their module context. -/

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
theorem clockDensity_pos {d : ℕ} (ω : FieldPair d) (x : Vec d) :
    0 < clockDensity ω x := Real.exp_pos _
end EinsteinRelation
