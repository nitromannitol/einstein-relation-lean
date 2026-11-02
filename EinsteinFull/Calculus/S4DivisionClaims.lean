import EinsteinFull.Calculus.S4DivisionVector

/-!
# Named forms of the scalar and vector division claims

`ScalarClaim` and `VectorClaim` are the statements proved in `division_scalar` and
`division_vector` with the constant `K` as a parameter, so that later lemmas can take them as
hypotheses.
-/

open Finset

namespace EinsteinFull

/-- The scalar estimate of `division_scalar`, for a given constant. -/
def ScalarClaim (d : ℕ) (C₁ Λ K : ℝ) : Prop :=
  ∀ (m η lam T χ0 : ℝ) (e : ℕ → ℝ) (hs0 : 0 < |lam|) (hs1 : |lam| ≤ Real.exp (-1)),
    m ≠ 0 → η ≠ 0 → |m⁻¹| ≤ Λ → |η⁻¹| ≤ Λ → (∀ j, |e j| ≤ C₁) → |χ0| ≤ C₁ →
    |T| ≤ |lam| ^ d * (1 + Real.log (1 / |lam|)) →
    |η - m - ∑ j ∈ range d, e j * lam ^ (j + 1) + 2 * χ0 * T| ≤
      C₁ * |lam| ^ d * expansionModulus |lam| hs0 hs1 →
    |η⁻¹ - ∑ n ∈ range (d + 1), recipSeq m e n * lam ^ n - (2 * χ0 / m ^ 2) * T| ≤
      K * |lam| ^ d * expansionModulus |lam| hs0 hs1

/-- The vector estimate of `division_vector`, for a given constant. -/
def VectorClaim (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ) (C₁ Λ K : ℝ) :
    Prop :=
  ∀ (m η lam T χ0 : ℝ) (e : ℕ → ℝ) (a : ℕ → E) (χv ell : E)
    (hs0 : 0 < |lam|) (hs1 : |lam| ≤ Real.exp (-1)),
    m ≠ 0 → η ≠ 0 → |m⁻¹| ≤ Λ → |η⁻¹| ≤ Λ → (∀ j, |e j| ≤ C₁) → (∀ k, ‖a k‖ ≤ C₁) →
    |χ0| ≤ C₁ → ‖χv‖ ≤ C₁ →
    |T| ≤ |lam| ^ d * (1 + Real.log (1 / |lam|)) →
    |η - m - ∑ j ∈ range d, e j * lam ^ (j + 1) + 2 * χ0 * T| ≤
      C₁ * |lam| ^ d * expansionModulus |lam| hs0 hs1 →
    ‖ell - ∑ k ∈ range (d + 1), lam ^ (k + 1) • a k + (2 * lam * T) • χv‖ ≤
      C₁ * |lam| ^ (d + 1) * expansionModulus |lam| hs0 hs1 →
    ‖η⁻¹ • ell - ∑ n ∈ range (d + 1), lam ^ (n + 1) •
        (∑ k ∈ range (n + 1), recipSeq m e (n - k) • a k) -
      (lam * T) • ((-2 / m) • χv + (2 * χ0 / m ^ 2) • a 0)‖ ≤
      K * |lam| ^ (d + 1) * expansionModulus |lam| hs0 hs1

theorem division_scalar_claim (d : ℕ) (hd : 2 ≤ d) (C₁ Λ : ℝ) (hC₁ : 0 ≤ C₁) (hΛ : 0 ≤ Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ ScalarClaim d C₁ Λ K :=
  division_scalar d hd C₁ Λ hC₁ hΛ

theorem division_vector_claim {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (d : ℕ)
    (hd : 2 ≤ d) (C₁ Λ : ℝ) (hC₁ : 0 ≤ C₁) (hΛ : 0 ≤ Λ) :
    ∃ K : ℝ, 0 ≤ K ∧ VectorClaim E d C₁ Λ K :=
  division_vector d hd C₁ Λ hC₁ hΛ

end EinsteinFull
