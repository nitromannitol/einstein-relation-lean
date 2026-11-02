import EinsteinRelation.Sharpness.Fields
import EinsteinRelation.Sharpness.RankOne
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Const
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.LinearCombination

/-! # Divergence of the first coefficient column

Source: `paper/main.tex`, `eq.sharp-map` and `eq.sharp-coefficients`, lines 1218–1231.
The coefficient `a = j B Bᵀ` is the one of `EinsteinRelation.Sharpness.RankOne`, with
`B = inverseCandidate` and `j = jacobianFactor`.

For `g = ∇ψ` with `1 + gᵢ ≠ 0`, the first column of the coefficient is the explicit vector
`a eᵢ = (1 + |g|²/(1 + gᵢ)) eᵢ - g`. Its diagonal entry is `coefficient_diagonal`, and each
off-diagonal entry in column `i` is `-gₖ`. Differentiating this column gives the second-jet
formula. Every second derivative keeps the order of the actual `coordinateDerivative`
applications, and no mixed-derivative commutation is used.
-/

open scoped BigOperators

namespace EinsteinRelation.Sharpness

/-! ### Entries of the first coefficient column -/

/-- Entrywise formula for the candidate inverse, unfolding the rank-one definition. -/
private theorem inverseCandidate_entry {d : ℕ} (i : Fin d) (g : Vec d) (j k : Fin d) :
    inverseCandidate i g j k =
      (if j = k then (1 : ℝ) else 0) - (jacobianFactor i g)⁻¹ * (unitVector i j * g k) := by
  simp only [inverseCandidate, outer, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Matrix.one_apply]

/-- Each coefficient entry is the Jacobian factor times an explicit finite sum. -/
private theorem coefficient_entry_eq_sum {d : ℕ} (i : Fin d) (g : Vec d) (j k : Fin d) :
    coefficient i g j k = jacobianFactor i g *
      ∑ l, inverseCandidate i g j l * inverseCandidate i g k l := by
  simp only [coefficient, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
    Matrix.transpose_apply]

/-- Off the diagonal, the first column of the coefficient is `-gₖ`. -/
private theorem coefficient_entry_offdiag {d : ℕ} (i k : Fin d) (g : Vec d)
    (hj : jacobianFactor i g ≠ 0) (hk : k ≠ i) : coefficient i g k i = -g k := by
  have hke : unitVector i k = 0 := by simp [unitVector, hk]
  have hii : unitVector i i = 1 := by simp [unitVector]
  have hBkk : inverseCandidate i g k k = 1 := by
    simp [inverseCandidate_entry, hke]
  have hBik : inverseCandidate i g i k = -((jacobianFactor i g)⁻¹ * g k) := by
    rw [inverseCandidate_entry, hii, if_neg (Ne.symm hk)]
    ring
  rw [coefficient_entry_eq_sum, Finset.sum_eq_single k]
  · show jacobianFactor i g * (inverseCandidate i g k k * inverseCandidate i g i k) = -g k
    rw [hBkk, hBik, one_mul, mul_neg, mul_inv_cancel_left₀ hj]
  · intro b _ hb
    show inverseCandidate i g k b * inverseCandidate i g i b = 0
    simp [inverseCandidate_entry, hke, Ne.symm hb]
  · intro h
    exact absurd (Finset.mem_univ k) h

/-- The first column of the coefficient, entrywise: `a eᵢ = (1 + |g|²/(1+gᵢ)) eᵢ - g`. -/
private theorem coefficient_entry_column {d : ℕ} (i k : Fin d) (g : Vec d)
    (hj : jacobianFactor i g ≠ 0) :
    coefficient i g k i = unitVector i k * (1 + euclideanSq g / (1 + g i)) - g k := by
  by_cases hk : k = i
  · have hii : unitVector i i = 1 := by simp [unitVector]
    rw [hk, coefficient_diagonal i g hj, hii]
    ring
  · have hke : unitVector i k = 0 := by simp [unitVector, hk]
    rw [coefficient_entry_offdiag i k g hj hk, hke]
    ring

/-- Summing a unit vector against `f` picks out the entry `f i`. -/
private theorem sum_unitVector_mul {d : ℕ} (i : Fin d) (f : Fin d → ℝ) :
    ∑ k, unitVector i k * f k = f i := by
  rw [Finset.sum_eq_single i]
  · simp [unitVector]
  · intro k _ hk
    simp [unitVector, hk]
  · intro h
    exact absurd (Finset.mem_univ i) h

/-! ### Smoothness and differentiability of coordinate derivatives -/

/-- The derivative of a `C^∞` scalar function is `C^∞`, as a map into the dual space. -/
private theorem contDiff_fderiv_top' {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) :=
  hf.fderiv_right (le_of_eq ENat.coe_top_add_one)

/-- Coordinate derivatives of a `C^∞` scalar function are `C^∞`. -/
private theorem contDiff_coordinateDerivative' {d : ℕ} {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => coordinateDerivative i f x) := by
  unfold coordinateDerivative
  exact (contDiff_fderiv_top' hf).clm_apply contDiff_const

/-- Each coordinate derivative of a `C^∞` scalar function is differentiable everywhere. -/
private theorem differentiableAt_coordinateDerivative' {d : ℕ} {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (i : Fin d) (y : Vec d) :
    DifferentiableAt ℝ (fun x => coordinateDerivative i ψ x) y :=
  (contDiff_coordinateDerivative' hψ i).differentiable (by simp) y

/-! ### Coordinate-derivative rules at a point of differentiability -/

/-- The coordinate derivative of a sum of two differentiable functions. -/
private theorem coordinateDerivative_add_fn {d : ℕ} (j : Fin d) {f g : Vec d → ℝ} {x : Vec d}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    coordinateDerivative j (fun y => f y + g y) x =
      coordinateDerivative j f x + coordinateDerivative j g x := by
  unfold coordinateDerivative
  rw [fderiv_fun_add hf hg, ContinuousLinearMap.add_apply]

/-- The coordinate derivative of a difference of two differentiable functions. -/
private theorem coordinateDerivative_sub_fn {d : ℕ} (j : Fin d) {f g : Vec d → ℝ} {x : Vec d}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    coordinateDerivative j (fun y => f y - g y) x =
      coordinateDerivative j f x - coordinateDerivative j g x := by
  unfold coordinateDerivative
  rw [fderiv_fun_sub hf hg, ContinuousLinearMap.sub_apply]

/-- The coordinate derivative of a constant multiple. -/
private theorem coordinateDerivative_const_mul_fn {d : ℕ} (j : Fin d) (c : ℝ) {f : Vec d → ℝ}
    {x : Vec d} (hf : DifferentiableAt ℝ f x) :
    coordinateDerivative j (fun y => c * f y) x = c * coordinateDerivative j f x := by
  unfold coordinateDerivative
  rw [fderiv_const_mul hf c, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- The product rule for coordinate derivatives. -/
private theorem coordinateDerivative_mul_fn {d : ℕ} (j : Fin d) {f g : Vec d → ℝ} {x : Vec d}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    coordinateDerivative j (fun y => f y * g y) x =
      f x * coordinateDerivative j g x + g x * coordinateDerivative j f x := by
  unfold coordinateDerivative
  rw [fderiv_fun_mul hf hg]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

/-- A constant function has zero coordinate derivative. The lemma for the constant function
`fun _ => c` is `fderiv_const_apply`; `fderiv_const` is stated for `Function.const`. -/
private theorem coordinateDerivative_const_fn {d : ℕ} (j : Fin d) (c : ℝ) (x : Vec d) :
    coordinateDerivative j (fun _ : Vec d => c) x = 0 := by
  unfold coordinateDerivative
  rw [fderiv_const_apply, ContinuousLinearMap.zero_apply]

/-- Adding a constant does not change the coordinate derivative. -/
private theorem coordinateDerivative_const_add_fn {d : ℕ} (j : Fin d) (c : ℝ)
    {f : Vec d → ℝ} {x : Vec d} (hf : DifferentiableAt ℝ f x) :
    coordinateDerivative j (fun y => c + f y) x = coordinateDerivative j f x := by
  have h : coordinateDerivative j (fun y => c + f y) x =
      coordinateDerivative j (fun _ : Vec d => c) x + coordinateDerivative j f x :=
    coordinateDerivative_add_fn j (differentiableAt_const c) hf
  rw [h, coordinateDerivative_const_fn j c x, zero_add]

/-- The coordinate derivative of a finite sum of differentiable functions. -/
private theorem coordinateDerivative_sum_fn {d : ℕ} (j : Fin d) (A : Fin d → Vec d → ℝ)
    {x : Vec d} (hA : ∀ m, DifferentiableAt ℝ (A m) x) :
    coordinateDerivative j (fun y => ∑ m, A m y) x = ∑ m, coordinateDerivative j (A m) x := by
  unfold coordinateDerivative
  rw [fderiv_fun_sum (fun m _ => hA m), ContinuousLinearMap.sum_apply]

/-- The coordinate derivative of the reciprocal of a nonvanishing differentiable function. The
proof differentiates the identity `u * u⁻¹ = 1`, which holds on all of `Vec d`. -/
private theorem coordinateDerivative_inv_fn {d : ℕ} (j : Fin d) {u : Vec d → ℝ} {x : Vec d}
    (hu : ∀ y, u y ≠ 0) (hd : DifferentiableAt ℝ u x) :
    coordinateDerivative j (fun y => (u y)⁻¹) x =
      -((u x)⁻¹ ^ 2) * coordinateDerivative j u x := by
  have hinv : DifferentiableAt ℝ (fun y => (u y)⁻¹) x := hd.fun_inv (hu x)
  have hmul : (fun y => u y * (u y)⁻¹) = fun _ => (1 : ℝ) :=
    funext fun y => mul_inv_cancel₀ (hu y)
  have h0 : coordinateDerivative j (fun y => u y * (u y)⁻¹) x =
      u x * coordinateDerivative j (fun y => (u y)⁻¹) x +
        (u x)⁻¹ * coordinateDerivative j u x :=
    coordinateDerivative_mul_fn j hd hinv
  rw [hmul, coordinateDerivative_const_fn j 1 x] at h0
  have hx : u x * (u x)⁻¹ = 1 := mul_inv_cancel₀ (hu x)
  linear_combination (-((u x)⁻¹)) * h0 - (coordinateDerivative j (fun y => (u y)⁻¹) x) * hx

/-! ### The divergence of the first coefficient column -/

/-- Source: `paper/main.tex`, `eq.sharp-map` and `eq.sharp-coefficients`, lines 1218–1231.
If `ψ` is `C^∞` and the jacobian factor `1 + ∂ᵢψ` never vanishes, the divergence of the first
column `a e₁` is the explicit second-jet formula. Each `∂ᵢ∂ₖψ` is the actual
`coordinateDerivative i (coordinateDerivative k ψ)`, with the order preserved. -/
theorem divergence_coefficientField_column_eq_jet :
    ∀ {d : ℕ} (i : Fin d) (ψ : Vec d → ℝ),
    ContDiff ℝ (⊤ : ℕ∞) ψ → (∀ y, jacobianFactor i (gradient ψ y) ≠ 0) → ∀ x : Vec d,
    divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x =
      -(∑ k : Fin d, coordinateDerivative k (coordinateDerivative k ψ) x) +
      (2 * ∑ k : Fin d, gradient ψ x k * coordinateDerivative i (coordinateDerivative k ψ) x) /
        (1+gradient ψ x i) -
      euclideanSq (gradient ψ x) * coordinateDerivative i (coordinateDerivative i ψ) x /
        (1+gradient ψ x i)^2 := by
  intro d i ψ hψ hj x
  -- Differentiability of the components of the gradient, and of the energy `|∇ψ|²`.
  have hgd : ∀ (m : Fin d) (y : Vec d), DifferentiableAt ℝ (fun z => gradient ψ z m) y :=
    fun m y => differentiableAt_coordinateDerivative' hψ m y
  have hgd_cd : ∀ (k : Fin d) (y : Vec d),
      coordinateDerivative k (fun z => gradient ψ z k) y =
        coordinateDerivative k (coordinateDerivative k ψ) y :=
    fun k y => rfl
  have hSfun : (fun z => euclideanSq (gradient ψ z)) =
      fun z => ∑ m, gradient ψ z m * gradient ψ z m := rfl
  have hSdiff : ∀ y, DifferentiableAt ℝ (fun z => euclideanSq (gradient ψ z)) y := by
    intro y
    rw [hSfun]
    exact DifferentiableAt.fun_sum fun m _ => (hgd m y).fun_mul (hgd m y)
  -- The jacobian factor, its reciprocal, and the rational part of the clock density.
  have hu_d : ∀ y, DifferentiableAt ℝ (fun z => 1 + gradient ψ z i) y :=
    fun y => (differentiableAt_const (1 : ℝ)).fun_add (hgd i y)
  have hw_d : ∀ y, DifferentiableAt ℝ (fun z => (1 + gradient ψ z i)⁻¹) y :=
    fun y => (hu_d y).fun_inv (hj y)
  have hphi_d : ∀ y, DifferentiableAt ℝ
      (fun z => 1 + euclideanSq (gradient ψ z) * (1 + gradient ψ z i)⁻¹) y :=
    fun y => (differentiableAt_const (1 : ℝ)).fun_add ((hSdiff y).fun_mul (hw_d y))
  have hSw_d : DifferentiableAt ℝ
      (fun y => euclideanSq (gradient ψ y) * (1 + gradient ψ y i)⁻¹) x :=
    (hSdiff x).fun_mul (hw_d x)
  -- Derivatives of the jacobian factor, its reciprocal, and the energy.
  have hu_cd : coordinateDerivative i (fun z => 1 + gradient ψ z i) x =
      coordinateDerivative i (coordinateDerivative i ψ) x :=
    coordinateDerivative_const_add_fn i 1 (hgd i x)
  have h3 : coordinateDerivative i (fun z => (1 + gradient ψ z i)⁻¹) x =
      -((1 + gradient ψ x i)⁻¹ ^ 2) * coordinateDerivative i (fun z => 1 + gradient ψ z i) x :=
    coordinateDerivative_inv_fn i (u := fun y => 1 + gradient ψ y i) (fun y => hj y) (hu_d x)
  have hSd : coordinateDerivative i (fun z => euclideanSq (gradient ψ z)) x =
      2 * ∑ m, gradient ψ x m * coordinateDerivative i (coordinateDerivative m ψ) x := by
    have hsum : coordinateDerivative i (fun z => ∑ m, gradient ψ z m * gradient ψ z m) x =
        ∑ m, coordinateDerivative i (fun z => gradient ψ z m * gradient ψ z m) x :=
      coordinateDerivative_sum_fn i (fun m z => gradient ψ z m * gradient ψ z m)
        (fun m => (hgd m x).fun_mul (hgd m x))
    have hterm2 : ∀ m, coordinateDerivative i (fun z => gradient ψ z m * gradient ψ z m) x =
        2 * (gradient ψ x m * coordinateDerivative i (coordinateDerivative m ψ) x) := by
      intro m
      rw [coordinateDerivative_mul_fn i (hgd m x) (hgd m x)]
      change gradient ψ x m * coordinateDerivative i (coordinateDerivative m ψ) x +
          gradient ψ x m * coordinateDerivative i (coordinateDerivative m ψ) x =
        2 * (gradient ψ x m * coordinateDerivative i (coordinateDerivative m ψ) x)
      ring
    rw [hSfun, hsum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun m _ => hterm2 m
  -- The `i`-th derivative of the rational part `1 + |∇ψ|² (1+∂ᵢψ)⁻¹`.
  have hphi_cd : coordinateDerivative i
      (fun y => 1 + euclideanSq (gradient ψ y) * (1 + gradient ψ y i)⁻¹) x =
      euclideanSq (gradient ψ x) *
          (-((1 + gradient ψ x i)⁻¹ ^ 2) * coordinateDerivative i (coordinateDerivative i ψ) x) +
        (1 + gradient ψ x i)⁻¹ *
          (2 * ∑ m, gradient ψ x m * coordinateDerivative i (coordinateDerivative m ψ) x) := by
    rw [coordinateDerivative_const_add_fn i 1 hSw_d,
      coordinateDerivative_mul_fn i (hSdiff x) (hw_d x), h3, hu_cd, hSd]
  -- The first column is `(1 + |∇ψ|²(1+∂ᵢψ)⁻¹) eᵢ - ∇ψ`, entrywise.
  have hcol : ∀ (y : Vec d) (k : Fin d), (coefficientField i ψ y).mulVec (unitVector i) k =
      unitVector i k * (1 + euclideanSq (gradient ψ y) * (1 + gradient ψ y i)⁻¹) -
        gradient ψ y k := by
    intro y k
    have h : (coefficientField i ψ y).mulVec (unitVector i) k = coefficientField i ψ y k i := by
      simp [Matrix.mulVec, dotProduct, unitVector, Pi.single_apply, mul_ite]
    have h2 : coefficientField i ψ y k i = unitVector i k *
        (1 + euclideanSq (gradient ψ y) / (1 + gradient ψ y i)) - gradient ψ y k :=
      coefficient_entry_column i k (gradient ψ y) (hj y)
    rw [h, h2, div_eq_mul_inv]
  have hdiv : divergence (fun y => (coefficientField i ψ y).mulVec (unitVector i)) x =
      ∑ k, coordinateDerivative k (fun y => unitVector i k *
        (1 + euclideanSq (gradient ψ y) * (1 + gradient ψ y i)⁻¹) - gradient ψ y k) x := by
    unfold divergence
    exact Finset.sum_congr rfl fun k _ =>
      congrArg (fun F => coordinateDerivative k F x) (funext fun y => hcol y k)
  -- Each component of the divergence sum, where the constant `unitVector i k` multiplies.
  have hterm : ∀ k : Fin d, coordinateDerivative k (fun y => unitVector i k *
      (1 + euclideanSq (gradient ψ y) * (1 + gradient ψ y i)⁻¹) - gradient ψ y k) x =
      unitVector i k * coordinateDerivative k
        (fun y => 1 + euclideanSq (gradient ψ y) * (1 + gradient ψ y i)⁻¹) x -
        coordinateDerivative k (coordinateDerivative k ψ) x := by
    intro k
    rw [coordinateDerivative_sub_fn k ((hphi_d x).const_mul (unitVector i k)) (hgd k x),
      coordinateDerivative_const_mul_fn k (unitVector i k) (hphi_d x), hgd_cd k x]
  rw [hdiv]
  simp only [hterm]
  rw [Finset.sum_sub_distrib, sum_unitVector_mul, hphi_cd, div_eq_mul_inv, div_eq_mul_inv,
    ← inv_pow]
  ring

end EinsteinRelation.Sharpness
