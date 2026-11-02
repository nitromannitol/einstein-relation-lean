import EinsteinRelation.Environment.Basic
import EinsteinRelation.Correctors.HeatSmoothing
import EinsteinRelation.Carriers.DensityAnnealedTwins
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-! # Production twin of the scalar averaging field predicate

`IsScalarAveragingField` mirrors the frozen definition in
`EinsteinRelation/Frozen/Correctors/IsScalarAveragingField.lean`. Production modules may not
import the frozen files, so the body is copied. The only replacement is `reducedReferenceLaw`,
which points to its production twin `EinsteinRelation.Carriers.reducedReferenceLaw`. The
smoothing operator `heatSmoothed` and the Euclidean objects are already production definitions
and are used unchanged.
-/

open MeasureTheory
open EinsteinRelation.Correctors

noncomputable section

namespace EinsteinRelation.Carriers

/-- Stationary fields are identified with functions of the environment (`paper/main.tex:241`),
`f(x, ω) = f(T_x ω)`. The field `f_R` is such a function that depends only on the environment in
`B_{33R}` (`paper/main.tex:961`) and satisfies, for every `m ∈ [2, ∞)` and every `t ≥ 0`,
`‖H_t f_R‖_{L^m(Q)} ≤ M_m ((1+t)^{-1/2} + R^{-1})` (`paper/main.tex:962-964`). The constants
`M m` are the values of the family `M`, which does not depend on `R`. The norms are taken on the
reduced law of `Q` (`paper/main.tex:198-208`).
Production twin of `EinsteinRelation.Frozen.Correctors.IsScalarAveragingField`
(`EinsteinRelation/Frozen/Correctors/IsScalarAveragingField.lean`), with the same body. -/
def IsScalarAveragingField {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (M : ℝ → ℝ)
    (R : ℝ) (f : FieldPair d → ℝ) : Prop :=
  Measurable[localSigma {y : Vec d | euclideanNorm (y - (0 : Vec d)) < 33 * R}] f ∧
    ∀ m : ℝ, 2 ≤ m → ∀ t : ℝ, 0 ≤ t →
      eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) (reducedReferenceLaw Q) ≤
        ENNReal.ofReal (M m * ((Real.sqrt (1 + t))⁻¹ + R⁻¹))

end EinsteinRelation.Carriers

end
