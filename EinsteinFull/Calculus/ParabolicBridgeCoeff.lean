import EinsteinFull.Calculus.S5CoefficientSupport
import EllipticRegularity.Parabolic.ParabolicDef

/-!
# Ellipticity of the rescaled coefficient

A symmetric matrix `ω` with `Λ⁻¹|ξ|² ≤ ξ·ωξ ≤ Λ|ξ|²` gives `Λ • ω` the library ellipticity
`IsEllipticMatrix 1 (Λ²)`, including the inverse coercivity.
-/

noncomputable section
namespace EinsteinFull.ParabolicBridge

open PDE

variable {d : ℕ}

theorem s5Bil_eq_vecDot (M : Mat d) (η ξ : Vec d) :
    EinsteinFull.s5Bil (fun j k => M j k) η ξ = vecDot η (matVecMul M ξ) := by
  unfold EinsteinFull.s5Bil vecDot matVecMul
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

theorem isEllipticMatrix_smul_of_symm_bounds {Λ : ℝ} (hΛ : 1 ≤ Λ) {ω : Mat d}
    (hsym : ω.transpose = ω)
    (hlow : ∀ ξ : Vec d, Λ⁻¹ * vecNormSq ξ ≤ vecDot ξ (matVecMul ω ξ))
    (hup : ∀ ξ : Vec d, vecDot ξ (matVecMul ω ξ) ≤ Λ * vecNormSq ξ) :
    IsEllipticMatrix 1 (Λ ^ 2) (Λ • ω) := by
  have hΛ0 : 0 < Λ := by linarith
  have hΛ2 : 1 ≤ Λ ^ 2 := by nlinarith
  have hAm : ∀ ξ : Vec d, matVecMul (Λ • ω) ξ = Λ • matVecMul ω ξ := by
    intro ξ
    funext i
    simp only [matVecMul, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hAdot : ∀ ξ : Vec d, vecDot ξ (matVecMul (Λ • ω) ξ) = Λ * vecDot ξ (matVecMul ω ξ) := by
    intro ξ
    rw [hAm]
    unfold vecDot
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have hcoer : ∀ ξ : Vec d, 1 * vecNormSq ξ ≤ vecDot ξ (matVecMul (Λ • ω) ξ) := by
    intro ξ
    rw [hAdot]
    calc 1 * vecNormSq ξ = Λ * (Λ⁻¹ * vecNormSq ξ) := by field_simp
      _ ≤ Λ * vecDot ξ (matVecMul ω ξ) := mul_le_mul_of_nonneg_left (hlow ξ) hΛ0.le
  have hupA : ∀ ξ : Vec d, vecDot ξ (matVecMul (Λ • ω) ξ) ≤ Λ ^ 2 * vecNormSq ξ := by
    intro ξ
    rw [hAdot]
    calc Λ * vecDot ξ (matVecMul ω ξ) ≤ Λ * (Λ * vecNormSq ξ) :=
          mul_le_mul_of_nonneg_left (hup ξ) hΛ0.le
      _ = Λ ^ 2 * vecNormSq ξ := by ring
  have hS : EinsteinFull.S5Elliptic (fun j k => (Λ • ω) j k) (Λ ^ 2) := by
    refine ⟨hΛ2, ?_, ?_, ?_⟩
    · intro j k
      have h1 : ω k j = ω j k := by
        have := congrFun (congrFun hsym j) k
        simpa [Matrix.transpose_apply] using this
      simp only [Matrix.smul_apply, smul_eq_mul, h1]
    · intro ξ
      rw [s5Bil_eq_vecDot, ← vecNormSq_eq_sum_sq]
      have hN := vecNormSq_nonneg ξ
      have h1 : (Λ ^ 2)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hΛ2
      calc (Λ ^ 2)⁻¹ * vecNormSq ξ ≤ 1 * vecNormSq ξ := mul_le_mul_of_nonneg_right h1 hN
        _ ≤ _ := hcoer ξ
    · intro ξ
      rw [s5Bil_eq_vecDot, ← vecNormSq_eq_sum_sq]
      exact hupA ξ
  -- invertibility
  have hinj : Function.Injective (Λ • ω).mulVec := by
    intro x y hxy
    have hz : (Λ • ω).mulVec (x - y) = 0 := by rw [Matrix.mulVec_sub, hxy, sub_self]
    have hz2 : vecDot (x - y) (matVecMul (Λ • ω) (x - y)) = 0 := by
      have : matVecMul (Λ • ω) (x - y) = 0 := hz
      rw [this]
      simp [vecDot]
    have h3 := hcoer (x - y)
    have h4 : vecNormSq (x - y) = 0 :=
      le_antisymm (by linarith) (vecNormSq_nonneg _)
    have h5 : x - y = 0 := vecNormSq_eq_zero h4
    exact sub_eq_zero.mp h5
  have hdet : IsUnit (Λ • ω).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp ((Matrix.mulVec_injective_iff_isUnit).mp hinj)
  refine ⟨one_pos, hΛ2, hcoer, ?_⟩
  intro ξ
  set A : Mat d := Λ • ω with hA
  set η : Vec d := matVecMul A⁻¹ ξ with hη
  have hAη : matVecMul A η = ξ := by
    have : A.mulVec ((A⁻¹).mulVec ξ) = ξ := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv A hdet, Matrix.one_mulVec]
    exact this
  have hN : EinsteinFull.s5Bil (fun j k => A j k) ξ η = vecNormSq ξ := by
    rw [s5Bil_eq_vecDot, hAη]
    rfl
  have hηξ : EinsteinFull.s5Bil (fun j k => A j k) η η = vecDot ξ (matVecMul A⁻¹ ξ) := by
    rw [s5Bil_eq_vecDot, hAη]
    rw [vecDot_comm]
  have hcs := EinsteinFull.s5Bil_sq_le hS ξ η
  have hξξ : EinsteinFull.s5Bil (fun j k => A j k) ξ ξ ≤ Λ ^ 2 * vecNormSq ξ := by
    rw [s5Bil_eq_vecDot]
    exact hupA ξ
  have hηη : 0 ≤ EinsteinFull.s5Bil (fun j k => A j k) η η :=
    EinsteinFull.s5Bil_self_nonneg hS η
  rw [hN] at hcs
  have hNn := vecNormSq_nonneg ξ
  rw [← hηξ]
  by_cases h0 : vecNormSq ξ = 0
  · rw [h0]
    simpa using hηη
  · have hpos : 0 < vecNormSq ξ := lt_of_le_of_ne hNn (Ne.symm h0)
    have h6 : vecNormSq ξ ^ 2 ≤ Λ ^ 2 * vecNormSq ξ *
        EinsteinFull.s5Bil (fun j k => A j k) η η :=
      hcs.trans (mul_le_mul_of_nonneg_right hξξ hηη)
    have h7 : vecNormSq ξ ≤ Λ ^ 2 * EinsteinFull.s5Bil (fun j k => A j k) η η := by
      by_contra hcon
      push_neg at hcon
      have := mul_lt_mul_of_pos_left hcon hpos
      nlinarith
    rw [inv_mul_le_iff₀ (by positivity)]
    exact h7

end EinsteinFull.ParabolicBridge
