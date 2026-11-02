import EinsteinRelation.Sharpness.CoefficientDivergenceJet
import Mathlib.Tactic.FunProp
open MeasureTheory
namespace EinsteinRelation.Sharpness
/-- Literal finite-jet expression for the divergence of the deformation coefficient column.
Source main.tex1218–1231; its actual field identity is proved below. The finite parameter carrier
uses the product of supremum norms only for this auxiliary calculus helper. All source spatial
Euclidean norms, matrix carriers and their conventions remain unchanged. -/
noncomputable def coefficientDivergenceProfile {d : ℕ} (i : Fin d) (z : Vec d × (Fin d → Fin d → ℝ)) : ℝ :=
  -(∑ k : Fin d, z.2 k k) + (2 * ∑ k : Fin d, z.1 k * z.2 i k) / (1 + z.1 i) -
    euclideanSq z.1 * z.2 i i / (1 + z.1 i)^2

/-- The finite-jet expression is the actual divergence on every smooth sample with nonvanishing
Jacobian. The Hessian entries keep the actual coordinate derivative order. -/
theorem divergence_coefficientField_column_eq_profile {d : ℕ} (i : Fin d) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hj : ∀ y, jacobianFactor i (gradient ψ y) ≠ 0) (x : Vec d) :
    divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x =
      coefficientDivergenceProfile i (gradient ψ x,
        fun m n => coordinateDerivative m (coordinateDerivative n ψ) x) :=
  divergence_coefficientField_column_eq_jet i ψ hψ hj x

/-- The literal rational profile is smooth at every parameter point with nonzero denominator. -/
theorem contDiffAt_coefficientDivergenceProfile {d : ℕ} (i : Fin d) (z : Vec d × (Fin d → Fin d → ℝ))
    (hj : 1 + z.1 i ≠ 0) : ContDiffAt ℝ (⊤ : ℕ∞) (coefficientDivergenceProfile i) z := by
  have hden : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Vec d × (Fin d → Fin d → ℝ) => 1 + q.1 i) z := by fun_prop
  have hsum : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Vec d × (Fin d → Fin d → ℝ) => ∑ k : Fin d, q.2 k k) z := by fun_prop
  have hdot : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Vec d × (Fin d → Fin d → ℝ) => 2 * ∑ k : Fin d, q.1 k * q.2 i k) z := by fun_prop
  have hnum : ContDiffAt ℝ (⊤ : ℕ∞) (fun q : Vec d × (Fin d → Fin d → ℝ) => euclideanSq q.1 * q.2 i i) z := by
    unfold euclideanSq dot
    fun_prop
  exact (hsum.neg.add (hdot.div hden hj)).sub (hnum.div (hden.pow 2) (pow_ne_zero 2 hj))
end EinsteinRelation.Sharpness
