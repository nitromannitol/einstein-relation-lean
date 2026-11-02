import EinsteinRelation.Sharpness.Fields
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Instances.Matrix

/-! # Smoothness of the sharpness coefficient, density, and physical fields

Source: `paper/main.tex`, lines 1212–1231 (`eq.sharp-map`, `eq.sharp-coefficients`).
If `ψ` is `C^∞` and the jacobian factor `1 + ∂ᵢψ` never vanishes, then the coefficient
`a = j B Bᵀ`, the clock density `μ`, the physical coefficient `μ⁻¹ a`, and the potential
`-(1/2) log μ` (on the region `μ > 0`) are `C^∞`.

Here `(⊤ : ℕ∞)` is the smooth regularity; bare `⊤` would be analytic in this Mathlib pin.
Smoothness is entrywise finite-dimensional scalar smoothness: no matrix norm is installed.
These statements do not give bounded derivatives, Lipschitz constants, stationarity,
finite range, or the construction of a random `ψ`; those remain separate obligations.
-/

open scoped BigOperators

namespace EinsteinRelation.Sharpness

/-- The derivative of a `C^∞` scalar function is `C^∞`, as a map into the dual space. -/
private theorem contDiff_fderiv_top {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
  hf.fderiv_right (le_of_eq ENat.coe_top_add_one)

/-- Coordinate derivatives of a `C^∞` scalar function are `C^∞`. -/
private theorem contDiff_coordinateDerivative {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => coordinateDerivative i f x) := by
  unfold coordinateDerivative
  exact (contDiff_fderiv_top hf).clm_apply contDiff_const

/-- Each component of the spatial gradient of a `C^∞` scalar function is `C^∞`. -/
private theorem contDiff_gradient_apply {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => gradient ψ x i) := by
  unfold gradient
  exact contDiff_coordinateDerivative hψ i

/-- The jacobian factor `1 + gᵢ` along the actual gradient is `C^∞`. -/
private theorem contDiff_jacobianFactor_gradient {d : ℕ} (i : Fin d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => jacobianFactor i (gradient ψ x)) := by
  unfold jacobianFactor
  exact contDiff_const.add (contDiff_gradient_apply hψ i)

/-- The reciprocal of the jacobian factor is `C^∞` where the factor never vanishes. -/
private theorem contDiff_jacobianFactor_gradient_inv {d : ℕ} (i : Fin d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hj : ∀ x, jacobianFactor i (gradient ψ x) ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => (jacobianFactor i (gradient ψ x))⁻¹) :=
  (contDiff_jacobianFactor_gradient i hψ).inv hj

/-- Entrywise formula for the candidate inverse, unfolding the rank-one definition. -/
private theorem inverseCandidate_apply_eq {d : ℕ} (i : Fin d) (g : Vec d) (j k : Fin d) :
    inverseCandidate i g j k =
      (if j = k then (1 : ℝ) else 0) - (jacobianFactor i g)⁻¹ * (unitVector i j * g k) := by
  simp only [inverseCandidate, outer, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]

/-- Each entry of the candidate inverse is `C^∞` along the actual gradient. -/
private theorem contDiff_inverseCandidate_entry {d : ℕ} (i : Fin d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hj : ∀ x, jacobianFactor i (gradient ψ x) ≠ 0)
    (j k : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => inverseCandidate i (gradient ψ x) j k) := by
  simp only [inverseCandidate_apply_eq]
  exact contDiff_const.sub ((contDiff_jacobianFactor_gradient_inv i hψ hj).mul
    (contDiff_const.mul (contDiff_gradient_apply hψ k)))

/-- The coefficient entry as the jacobian factor times an explicit finite sum. -/
private theorem coefficient_apply_eq_sum {d : ℕ} (i : Fin d) (g : Vec d) (j k : Fin d) :
    coefficient i g j k = jacobianFactor i g *
      ∑ l, inverseCandidate i g j l * inverseCandidate i g k l := by
  simp only [coefficient, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply]

/-- Every entry of the coefficient field is `C^∞` in the position variable. -/
theorem contDiff_coefficientField_entry {d : ℕ} (i : Fin d) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hj : ∀ x, jacobianFactor i (gradient ψ x) ≠ 0) :
    ∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => coefficientField i ψ x j k) := by
  intro j k
  have hsum : ContDiff ℝ (⊤ : ℕ∞) (fun x =>
      ∑ l, inverseCandidate i (gradient ψ x) j l * inverseCandidate i (gradient ψ x) k l) :=
    ContDiff.sum fun l _ =>
      (contDiff_inverseCandidate_entry i hψ hj j l).mul
        (contDiff_inverseCandidate_entry i hψ hj k l)
  simp only [coefficientField, coefficient_apply_eq_sum]
  exact (contDiff_jacobianFactor_gradient i hψ).mul hsum

/-- Each component of the first coefficient column `a e₁` is `C^∞`. -/
private theorem contDiff_firstColumn_component {d : ℕ} (i : Fin d) {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hj : ∀ x, jacobianFactor i (gradient ψ x) ≠ 0)
    (m : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y => (coefficientField i ψ y).mulVec (unitVector i) m) := by
  have h : ∀ y, (coefficientField i ψ y).mulVec (unitVector i) m =
      coefficientField i ψ y m i := by
    intro y
    simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, mul_ite]
  simp only [h]
  exact contDiff_coefficientField_entry i ψ hψ hj m i

/-- A vector field with `C^∞` components has `C^∞` divergence. -/
private theorem contDiff_divergence_of_components {d : ℕ} {F : Vec d → Vec d}
    (hF : ∀ m, ContDiff ℝ (⊤ : ℕ∞) (fun y => F y m)) :
    ContDiff ℝ (⊤ : ℕ∞) (divergence F) := by
  show ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑ m, coordinateDerivative m (fun y => F y m) x)
  exact ContDiff.sum fun m _ => contDiff_coordinateDerivative (hF m) m

/-- The clock density `μ = 1 + (δ/2) ∇·(a e₁)` is `C^∞`. -/
theorem contDiff_densityField {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hj : ∀ x, jacobianFactor i (gradient ψ x) ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (densityField i δ ψ) := by
  have hdiv : ContDiff ℝ (⊤ : ℕ∞)
      (divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i))) :=
    contDiff_divergence_of_components fun m => contDiff_firstColumn_component i hψ hj m
  show ContDiff ℝ (⊤ : ℕ∞) (fun x =>
    1 + δ / 2 * divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x)
  exact contDiff_const.add (contDiff_const.mul hdiv)

/-- The physical coefficient `μ⁻¹ a` is `C^∞` entrywise, and the potential
`-(1/2) log μ` is `C^∞`, on the region where the clock density is positive. -/
theorem contDiff_physicalFields {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hj : ∀ x, jacobianFactor i (gradient ψ x) ≠ 0)
    (hμ : ∀ x, 0 < densityField i δ ψ x) :
    (∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => physicalCoefficientField i δ ψ x j k)) ∧
      ContDiff ℝ (⊤ : ℕ∞) (potentialField i δ ψ) := by
  have hdens : ContDiff ℝ (⊤ : ℕ∞) (densityField i δ ψ) :=
    contDiff_densityField i δ ψ hψ hj
  have hinv : ContDiff ℝ (⊤ : ℕ∞) (fun x => (densityField i δ ψ x)⁻¹) :=
    hdens.inv fun x => (hμ x).ne'
  refine ⟨fun j k => ?_, ?_⟩
  · have key : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => (densityField i δ ψ x)⁻¹ * coefficientField i ψ x j k) :=
      hinv.mul (contDiff_coefficientField_entry i ψ hψ hj j k)
    simpa only [physicalCoefficientField, Matrix.smul_apply, smul_eq_mul] using key
  · have key : ContDiff ℝ (⊤ : ℕ∞)
        (fun x => -(1 / 2 : ℝ) * Real.log (densityField i δ ψ x)) :=
      contDiff_const.mul (hdens.log fun x => (hμ x).ne')
    exact key

/-- The spatial coefficient is continuous, from its entrywise smoothness. -/
theorem continuous_coefficientField {d : ℕ} (i : Fin d) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hj : ∀ x, jacobianFactor i (gradient ψ x) ≠ 0) :
    Continuous (coefficientField i ψ) :=
  continuous_matrix fun j k => (contDiff_coefficientField_entry i ψ hψ hj j k).continuous

/-- The physical coefficient is continuous on the region where the clock density is positive. -/
theorem continuous_physicalCoefficientField {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hj : ∀ x, jacobianFactor i (gradient ψ x) ≠ 0)
    (hμ : ∀ x, 0 < densityField i δ ψ x) :
    Continuous (physicalCoefficientField i δ ψ) :=
  continuous_matrix fun j k => ((contDiff_physicalFields i δ ψ hψ hj hμ).1 j k).continuous

/-- The physical potential is continuous on the region where the clock density is positive. -/
theorem continuous_potentialField {d : ℕ} (i : Fin d) (δ : ℝ) (ψ : Vec d → ℝ)
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hj : ∀ x, jacobianFactor i (gradient ψ x) ≠ 0)
    (hμ : ∀ x, 0 < densityField i δ ψ x) :
    Continuous (potentialField i δ ψ) :=
  (contDiff_physicalFields i δ ψ hψ hj hμ).2.continuous

end EinsteinRelation.Sharpness
