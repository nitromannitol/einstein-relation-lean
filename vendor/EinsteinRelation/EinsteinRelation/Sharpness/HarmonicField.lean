import EinsteinRelation.Sharpness.Fields
import EinsteinRelation.Sharpness.RankOne
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith

/-! # The harmonic identity and clock generator for the actual fields

`paper/main.tex`, `eq.sharp-harmonic` (1233–1235) and `eq.sharp-generator`
(1243–1250). Spatial derivatives and the density are the literal definitions,
not independent variables satisfying the conclusion as an extra premise.
-/

namespace EinsteinRelation.Sharpness

/-- The constructed spatial coefficient has the claimed constant harmonic flux. -/
theorem coefficientField_harmonic {d : ℕ} (i : Fin d) (ψ : Vec d → ℝ)
    (x : Vec d) (hj : jacobianFactor i (gradient ψ x) ≠ 0) :
    (coefficientField i ψ x).mulVec (unitVector i + gradient ψ x) = unitVector i :=
  coefficient_mulVec i (gradient ψ x) hj

/-- The scalar product with the force column is `1 - aᵢᵢ`. -/
theorem coefficientField_dot_gradient {d : ℕ} (i : Fin d) (ψ : Vec d → ℝ)
    (x : Vec d) (hj : jacobianFactor i (gradient ψ x) ≠ 0) :
    dot ((coefficientField i ψ x).mulVec (unitVector i)) (gradient ψ x) =
      1 - coefficientField i ψ x i i := by
  have hcol : ∀ k, (coefficientField i ψ x).mulVec (unitVector i) k =
      coefficientField i ψ x k i := by
    intro k
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply]
  have hsym := coefficient_transpose i (gradient ψ x)
  have hpair : dot ((coefficientField i ψ x).mulVec (unitVector i)) (gradient ψ x) =
      (coefficientField i ψ x).mulVec (gradient ψ x) i := by
    change (∑ k, (coefficientField i ψ x).mulVec (unitVector i) k * gradient ψ x k) =
      ∑ k, coefficientField i ψ x i k * gradient ψ x k
    apply Finset.sum_congr rfl
    intro k _
    rw [hcol k]
    have hs := congrArg (fun A : Mat d => A i k) hsym
    exact congrArg (fun z : ℝ => z * gradient ψ x k) hs
  rw [hpair]
  have h := congrArg (fun v : Vec d => v i) (coefficientField_harmonic i ψ x hj)
  rw [Matrix.mulVec_add] at h
  change (coefficientField i ψ x).mulVec (unitVector i) i +
    (coefficientField i ψ x).mulVec (gradient ψ x) i = unitVector i i at h
  rw [hcol i] at h
  simp only [unitVector, Pi.single_eq_same] at h
  linarith only [h]

/-- A constant minus a vector field has the negative divergence, including the
standard totalized derivative convention away from differentiability points. -/
theorem divergence_const_sub {d : ℕ} (c : Vec d) (F : Vec d → Vec d) (x : Vec d) :
    divergence (fun y => c - F y) x = -divergence F x := by
  unfold divergence coordinateDerivative
  simp only [Pi.sub_apply, fderiv_const_sub, ContinuousLinearMap.neg_apply, Finset.sum_neg_distrib]

/-- The actual gradient flux has divergence minus that of the force column. -/
theorem coefficientField_divergence_gradient {d : ℕ} (i : Fin d) (ψ : Vec d → ℝ)
    (hj : ∀ y, jacobianFactor i (gradient ψ y) ≠ 0) (x : Vec d) :
    divergence (fun y => (coefficientField i ψ y).mulVec (gradient ψ y)) x =
      -divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x := by
  have hfield : (fun y => (coefficientField i ψ y).mulVec (gradient ψ y)) =
      (fun y => unitVector i - (coefficientField i ψ y).mulVec (unitVector i)) := by
    funext y
    have h := coefficientField_harmonic i ψ y (hj y)
    rw [Matrix.mulVec_add] at h
    exact eq_sub_of_add_eq' h
  rw [hfield, divergence_const_sub]

/-- The literal constructed density gives the source's clock generator identity. -/
theorem clock_generator_identity {d : ℕ} (i : Fin d) (δ lam : ℝ) (ψ : Vec d → ℝ)
    (hδ : δ ≠ 0) (hj : ∀ y, jacobianFactor i (gradient ψ y) ≠ 0) (x : Vec d) :
    (1 / 2 : ℝ) * divergence (fun y => (coefficientField i ψ y).mulVec (gradient ψ y)) x +
      lam * dot ((coefficientField i ψ x).mulVec (unitVector i)) (gradient ψ x) =
    (1 - densityField i δ ψ x) / δ + lam * (1 - coefficientField i ψ x i i) := by
  rw [coefficientField_divergence_gradient i ψ hj x,
    coefficientField_dot_gradient i ψ x (hj x)]
  unfold densityField
  field_simp [hδ]
  ring

end EinsteinRelation.Sharpness
