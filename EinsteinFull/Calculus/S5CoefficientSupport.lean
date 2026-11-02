import Mathlib.Analysis.Complex.Basic
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Pointwise coefficient algebra for the weighted energy estimate

For a symmetric real matrix `A` with ellipticity constant `Λ`, written in explicit
coordinate sums, we prove the Cauchy–Schwarz inequality for the positive form,
the operator bound `|η·Aξ| ≤ Λ|η||ξ|`, and the complex versions needed for
`Re ΣΣ A_jk X_k conj X_j ≥ Λ⁻¹ Σ|X_j|²` and `|ΣΣ η_j A_jk X_k| ≤ 2Λ|η||X|`.
-/

open scoped BigOperators

noncomputable section
namespace EinsteinFull

section S5Coef

variable {d : ℕ}

/-- The coordinate bilinear form `η·Aξ`. -/
def s5Bil (A : Fin d → Fin d → ℝ) (η ξ : Fin d → ℝ) : ℝ := ∑ j, ∑ k, η j * A j k * ξ k

/-- Euclidean norm of a real coordinate vector. -/
def s5Nrm (ξ : Fin d → ℝ) : ℝ := Real.sqrt (∑ j, ξ j ^ 2)

/-- Euclidean norm of a complex coordinate vector. -/
def s5CNrm (X : Fin d → ℂ) : ℝ := Real.sqrt (∑ j, ‖X j‖ ^ 2)

/-- Symmetric ellipticity in explicit coordinates. -/
structure S5Elliptic (A : Fin d → Fin d → ℝ) (Λ : ℝ) : Prop where
  one_le : 1 ≤ Λ
  symm : ∀ j k, A j k = A k j
  lower : ∀ ξ : Fin d → ℝ, Λ⁻¹ * ∑ j, ξ j ^ 2 ≤ s5Bil A ξ ξ
  upper : ∀ ξ : Fin d → ℝ, s5Bil A ξ ξ ≤ Λ * ∑ j, ξ j ^ 2

variable {A : Fin d → Fin d → ℝ} {Λ : ℝ}

theorem s5Bil_symm (h : S5Elliptic A Λ) (η ξ : Fin d → ℝ) : s5Bil A η ξ = s5Bil A ξ η := by
  unfold s5Bil
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h.symm j k]
  ring

theorem s5Bil_self_nonneg (h : S5Elliptic A Λ) (ξ : Fin d → ℝ) : 0 ≤ s5Bil A ξ ξ :=
  le_trans (mul_nonneg (inv_nonneg.mpr (by linarith [h.one_le]))
    (Finset.sum_nonneg fun j _ => sq_nonneg _)) (h.lower ξ)

theorem s5Bil_sq_le (h : S5Elliptic A Λ) (η ξ : Fin d → ℝ) :
    s5Bil A η ξ ^ 2 ≤ s5Bil A η η * s5Bil A ξ ξ := by
  have hexp : ∀ s : ℝ, s5Bil A (η + s • ξ) (η + s • ξ) =
      s5Bil A ξ ξ * s ^ 2 + (2 * s5Bil A η ξ) * s + s5Bil A η η := by
    intro s
    have h1 : ∀ j k, (η + s • ξ) j * A j k * (η + s • ξ) k =
        η j * A j k * η k + s * (η j * A j k * ξ k) + s * (ξ j * A j k * η k) +
          s ^ 2 * (ξ j * A j k * ξ k) := by
      intro j k
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    have h2 : ∑ j, ∑ k, ξ j * A j k * η k = ∑ j, ∑ k, η j * A j k * ξ k :=
      s5Bil_symm h ξ η
    have h3 : s5Bil A η ξ = ∑ j, ∑ k, η j * A j k * ξ k := rfl
    have h4 : s5Bil A ξ ξ = ∑ j, ∑ k, ξ j * A j k * ξ k := rfl
    have h5 : s5Bil A η η = ∑ j, ∑ k, η j * A j k * η k := rfl
    have h6 : s5Bil A (η + s • ξ) (η + s • ξ) =
        ∑ j, ∑ k, (η + s • ξ) j * A j k * (η + s • ξ) k := rfl
    rw [h6, h3, h4, h5]
    simp only [h1, Finset.sum_add_distrib, ← Finset.mul_sum]
    rw [h2]
    ring
  have hd := discrim_le_zero (a := s5Bil A ξ ξ) (b := 2 * s5Bil A η ξ) (c := s5Bil A η η)
    (fun s => by
      have h0 := s5Bil_self_nonneg h (η + s • ξ)
      rw [hexp] at h0
      nlinarith [h0])
  unfold discrim at hd
  nlinarith [hd]

theorem s5Nrm_sq (η : Fin d → ℝ) : s5Nrm η ^ 2 = ∑ j, η j ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg fun j _ => sq_nonneg _)

theorem s5Bil_abs_le (h : S5Elliptic A Λ) (η ξ : Fin d → ℝ) :
    |s5Bil A η ξ| ≤ Λ * s5Nrm η * s5Nrm ξ := by
  have hΛ0 : 0 ≤ Λ := by linarith [h.one_le]
  have hη : s5Bil A η η ≤ Λ * s5Nrm η ^ 2 := by
    rw [s5Nrm_sq]
    exact h.upper η
  have hξ : s5Bil A ξ ξ ≤ Λ * s5Nrm ξ ^ 2 := by
    rw [s5Nrm_sq]
    exact h.upper ξ
  have hrhs : 0 ≤ Λ * s5Nrm η * s5Nrm ξ :=
    mul_nonneg (mul_nonneg hΛ0 (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) hrhs two_ne_zero).mp ?_
  rw [sq_abs]
  calc s5Bil A η ξ ^ 2 ≤ s5Bil A η η * s5Bil A ξ ξ := s5Bil_sq_le h η ξ
    _ ≤ (Λ * s5Nrm η ^ 2) * (Λ * s5Nrm ξ ^ 2) :=
        mul_le_mul hη hξ (s5Bil_self_nonneg h ξ) (mul_nonneg hΛ0 (sq_nonneg _))
    _ = (Λ * s5Nrm η * s5Nrm ξ) ^ 2 := by ring

theorem s5_re_sq_le (z : ℂ) : z.re ^ 2 ≤ ‖z‖ ^ 2 := by
  have h := Complex.sq_norm z
  rw [Complex.normSq_apply] at h
  nlinarith [sq_nonneg z.im]

theorem s5_im_sq_le (z : ℂ) : z.im ^ 2 ≤ ‖z‖ ^ 2 := by
  have h := Complex.sq_norm z
  rw [Complex.normSq_apply] at h
  nlinarith [sq_nonneg z.re]

theorem s5Nrm_re_le (X : Fin d → ℂ) : s5Nrm (fun k => (X k).re) ≤ s5CNrm X :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => s5_re_sq_le (X k))

theorem s5Nrm_im_le (X : Fin d → ℂ) : s5Nrm (fun k => (X k).im) ≤ s5CNrm X :=
  Real.sqrt_le_sqrt (Finset.sum_le_sum fun k _ => s5_im_sq_le (X k))

theorem s5CNrm_nonneg (X : Fin d → ℂ) : 0 ≤ s5CNrm X := Real.sqrt_nonneg _

theorem s5Nrm_nonneg (X : Fin d → ℝ) : 0 ≤ s5Nrm X := Real.sqrt_nonneg _

/-- Complex bilinear bound with a real left vector. -/
theorem s5_cbil_norm_le (h : S5Elliptic A Λ) (η : Fin d → ℝ) (X : Fin d → ℂ) :
    ‖∑ j, ∑ k, (η j : ℂ) * (A j k : ℂ) * X k‖ ≤ 2 * Λ * s5Nrm η * s5CNrm X := by
  have hΛ0 : 0 ≤ Λ := by linarith [h.one_le]
  have hre : (∑ j, ∑ k, (η j : ℂ) * (A j k : ℂ) * X k).re =
      s5Bil A η (fun k => (X k).re) := by
    simp only [Complex.re_sum, ← Complex.ofReal_mul, Complex.re_ofReal_mul, s5Bil]
  have him : (∑ j, ∑ k, (η j : ℂ) * (A j k : ℂ) * X k).im =
      s5Bil A η (fun k => (X k).im) := by
    simp only [Complex.im_sum, ← Complex.ofReal_mul, Complex.im_ofReal_mul, s5Bil]
  have h1 := Complex.norm_le_abs_re_add_abs_im (∑ j, ∑ k, (η j : ℂ) * (A j k : ℂ) * X k)
  rw [hre, him] at h1
  have h2 : |s5Bil A η (fun k => (X k).re)| ≤ Λ * s5Nrm η * s5CNrm X :=
    (s5Bil_abs_le h η _).trans
      (mul_le_mul_of_nonneg_left (s5Nrm_re_le X) (mul_nonneg hΛ0 (s5Nrm_nonneg η)))
  have h3 : |s5Bil A η (fun k => (X k).im)| ≤ Λ * s5Nrm η * s5CNrm X :=
    (s5Bil_abs_le h η _).trans
      (mul_le_mul_of_nonneg_left (s5Nrm_im_le X) (mul_nonneg hΛ0 (s5Nrm_nonneg η)))
  linarith only [h1, h2, h3]

/-- Coercivity of the complex Hermitian form. -/
theorem s5_coercive (h : S5Elliptic A Λ) (X : Fin d → ℂ) :
    Λ⁻¹ * ∑ j, ‖X j‖ ^ 2 ≤ (∑ j, ∑ k, (A j k : ℂ) * X k * (starRingEnd ℂ) (X j)).re := by
  have hre : (∑ j, ∑ k, (A j k : ℂ) * X k * (starRingEnd ℂ) (X j)).re =
      s5Bil A (fun k => (X k).re) (fun k => (X k).re) +
        s5Bil A (fun k => (X k).im) (fun k => (X k).im) := by
    unfold s5Bil
    rw [← Finset.sum_add_distrib, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib, Complex.re_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mul_assoc, Complex.re_ofReal_mul, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hre]
  have h1 := h.lower (fun k => (X k).re)
  have h2 := h.lower (fun k => (X k).im)
  have h3 : ∑ j, ‖X j‖ ^ 2 = ∑ j, (X j).re ^ 2 + ∑ j, (X j).im ^ 2 := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := Complex.sq_norm (X j)
    rw [Complex.normSq_apply] at this
    rw [this]
    ring
  rw [h3, mul_add]
  linarith only [h1, h2]

end S5Coef

end EinsteinFull
