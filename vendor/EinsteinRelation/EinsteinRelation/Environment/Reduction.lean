import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! # The coefficient and clock of the time change -/

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

theorem reduce_translate {d : ℕ} (ω : FieldPair d) (x : Vec d) :
    reduce (translate x ω) = translate x (reduce ω) := rfl

end EinsteinRelation
