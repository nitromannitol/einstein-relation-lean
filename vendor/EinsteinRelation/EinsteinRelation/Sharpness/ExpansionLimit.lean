import EinsteinRelation.Environment.Basic
import Mathlib.Topology.Algebra.GroupWithZero
import Mathlib.Topology.Algebra.Group.Basic
import Mathlib.Topology.Algebra.Monoid
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Algebra.Ring.Real
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.OrderClosed

/-! # Limit of the sharp clock-rate expansion

`paper/main.tex:1252–1272`, the end of the proof of Proposition 7.1. The exact clock identity
gives `η(λ) = 1 - δ λ (A(λ) - 1)` for small `λ`, where `A(λ)` tends to `a₁₁` as `λ ↓ 0`.
The scalar theorem shows that `(η(λ)⁻¹ - 1)/λ` tends to `δ (a₁₁ - 1)`. The vector theorem
transfers this limit to the first Euclidean coordinate of the expansion of `ℓ_X(λ)`.
-/

open Filter Topology

namespace EinsteinRelation.Sharpness

/-- Linearity of the Euclidean scalar product in its first argument under subtraction. -/
private theorem expansion_dot_sub_left {d : ℕ} (x y z : Vec d) :
    dot (x - y) z = dot x z - dot y z := by
  simp only [dot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

/-- Linearity of the Euclidean scalar product under scalar multiplication in its first slot. -/
private theorem expansion_dot_smul_left {d : ℕ} (c : ℝ) (x z : Vec d) :
    dot (c • x) z = c * dot x z := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc]

/-- Algebraic identity behind `(η⁻¹ - 1)/λ = δ x / η` for `η = 1 - δ λ x`. -/
private theorem expansion_inv_sub_one_div (δ lam x : ℝ) (hlam : lam ≠ 0)
    (hη : 1 - δ * lam * x ≠ 0) :
    ((1 - δ * lam * x)⁻¹ - 1) / lam = δ * x / (1 - δ * lam * x) := by
  rw [div_eq_div_iff hlam hη, sub_mul, inv_mul_cancel₀ hη, one_mul]
  ring

/-- Scalar limit of the clock rate: if `η(λ) = 1 - δ λ (A(λ) - 1)` for small `λ` with
`A(λ) → a₁₁` as `λ ↓ 0`, and `η(λ) ≠ 0` eventually, then `(η(λ)⁻¹ - 1)/λ → δ (a₁₁ - 1)`. -/
theorem sharp_expansion_scalar_limit {δ a11 : ℝ} (_hδ : 0 < δ) (eta A : ℝ → ℝ)
    (h_eta : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → eta lam = 1 - δ * lam * (A lam - 1))
    (hA : Tendsto A (𝓝[>] 0) (𝓝 a11))
    (h_ne : ∀ᶠ lam in 𝓝[>] 0, eta lam ≠ 0) :
    Tendsto (fun lam => ((eta lam)⁻¹ - 1) / lam) (𝓝[>] 0) (𝓝 (δ * (a11 - 1))) := by
  have hpos01 : Set.Ioc (0 : ℝ) 1 ∈ 𝓝[>] (0 : ℝ) := Ioc_mem_nhdsGT (by norm_num)
  have hlam : Tendsto (fun lam : ℝ => lam) (𝓝[>] 0) (𝓝 0) :=
    tendsto_nhdsWithin_of_tendsto_nhds tendsto_id
  have hB : Tendsto (fun lam => δ * (A lam - 1)) (𝓝[>] 0) (𝓝 (δ * (a11 - 1))) :=
    (hA.sub_const 1).const_mul δ
  have hprod : Tendsto (fun lam => lam * (δ * (A lam - 1))) (𝓝[>] 0) (𝓝 0) := by
    have h := hlam.mul hB
    rwa [zero_mul] at h
  have hlim : Tendsto (fun lam => 1 - lam * (δ * (A lam - 1))) (𝓝[>] 0) (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) (𝓝[>] 0) (𝓝 1)).sub hprod
    rwa [sub_zero] at h
  have heta : Tendsto eta (𝓝[>] 0) (𝓝 1) := by
    refine hlim.congr' ?_
    filter_upwards [hpos01] with lam hmem
    show 1 - lam * (δ * (A lam - 1)) = eta lam
    rw [h_eta lam hmem.1 hmem.2]
    ring
  have hquot : Tendsto (fun lam => δ * (A lam - 1) / eta lam) (𝓝[>] 0)
      (𝓝 (δ * (a11 - 1) / 1)) :=
    hB.div heta one_ne_zero
  rw [div_one] at hquot
  have key : (fun lam => ((eta lam)⁻¹ - 1) / lam) =ᶠ[𝓝[>] 0]
      (fun lam => δ * (A lam - 1) / eta lam) := by
    filter_upwards [hpos01, h_ne] with lam hmem hne
    show ((eta lam)⁻¹ - 1) / lam = δ * (A lam - 1) / eta lam
    rw [h_eta lam hmem.1 hmem.2] at hne ⊢
    exact expansion_inv_sub_one_div δ lam (A lam - 1) hmem.1.ne' hne
  exact hquot.congr' key.symm

/-- The first-coordinate form of the clock-rate limit. If `dot (v λ) e₁ = λ (η(λ))⁻¹` for
`λ > 0` and `dot Se₁ e₁ = 1`, then the normalized first-coordinate error
`dot (λ⁻¹ • v λ - Se₁) e₁ / λ` tends to `δ (a₁₁ - 1)`. -/
theorem sharp_expansion_vector_limit {d : ℕ} {δ a11 : ℝ} (_hδ : 0 < δ) (eta A : ℝ → ℝ)
    (h_eta : ∀ lam : ℝ, 0 < lam → lam ≤ 1 → eta lam = 1 - δ * lam * (A lam - 1))
    (hA : Tendsto A (𝓝[>] 0) (𝓝 a11))
    (h_ne : ∀ᶠ lam in 𝓝[>] 0, eta lam ≠ 0)
    (e1 : Vec d) (v : ℝ → Vec d)
    (hv : ∀ lam : ℝ, 0 < lam → dot (v lam) e1 = lam * (eta lam)⁻¹)
    (Se1 : Vec d) (hSe1 : dot Se1 e1 = 1) :
    Tendsto (fun lam => dot (lam⁻¹ • v lam - Se1) e1 / lam) (𝓝[>] 0)
      (𝓝 (δ * (a11 - 1))) := by
  refine (sharp_expansion_scalar_limit _hδ eta A h_eta hA h_ne).congr' ?_
  have hIoi : Set.Ioi (0 : ℝ) ∈ 𝓝[>] (0 : ℝ) := self_mem_nhdsWithin
  filter_upwards [hIoi] with lam hlam
  have hpos : 0 < lam := Set.mem_Ioi.mp hlam
  have hdot : dot (lam⁻¹ • v lam - Se1) e1 = (eta lam)⁻¹ - 1 := by
    rw [expansion_dot_sub_left, expansion_dot_smul_left, hv lam hpos, hSe1]
    rw [← mul_assoc, inv_mul_cancel₀ hpos.ne', one_mul]
  show ((eta lam)⁻¹ - 1) / lam = dot (lam⁻¹ • v lam - Se1) e1 / lam
  rw [hdot]

end EinsteinRelation.Sharpness
