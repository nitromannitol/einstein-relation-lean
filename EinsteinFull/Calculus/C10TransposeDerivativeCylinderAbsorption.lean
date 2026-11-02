import EinsteinFull.Calculus.C9LocalTimeTransposeDerivativeMoment
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

namespace C10

/-- Absorption on the parabolic cylinder with a constant uniform in the force and data. -/
theorem local_time_transpose_conditional_derivative_cylinder_absorption
    (d : ℕ) [Fact (2 ≤ d)] (Λ₀ : ℝ) (hΛ : 1 ≤ Λ₀) :
    ∃ C : ℝ, 0 < C ∧
    ∀ {r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
      {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)},
      IsComplexEnvironmentSemigroup Q i ζ P → IsComplexTransposeSemigroup Q P T →
    ∀ {f g : Lp ℂ 2 (reducedLaw Q)}, IsComplexTransposeGeneratorPair Q i ζ f g →
    ∀ (t : ℝ), 0 < t → ∀ (ρ : ℝ), Real.sqrt t ≤ ρ →
    ∀ (z : Vec d) (A : Set (FieldPair d)),
      (∫ x in {x | euclideanNorm (x - z) ≤ ρ}, ∫ s in Icc (t / 2) t,
        ∫ ω in A, ‖(T s.toNNReal g) (translate x ω)‖ ^ 2 ∂reducedLaw Q) ≤
      C * (1 + ‖ζ‖ * Real.sqrt t) ^ 4 / t ^ 2 *
        (∫ x in {x | euclideanNorm (x - z) ≤ 2 * ρ}, ∫ s in Icc (t / 4) t,
          ∫ ω in A, ‖(T s.toNNReal f) (translate x ω)‖ ^ 2 ∂reducedLaw Q) := by
  obtain ⟨B, H, Y, hB, hH, hY, habs⟩ :=
    EinsteinFull.Blueprint.local_time_transpose_conditional_derivative_cylinder_absorption d
  let L := Real.exp (2 * Λ₀) * Λ₀
  have hL : 0 < L := mul_pos (Real.exp_pos _) (lt_of_lt_of_le zero_lt_one hΛ)
  let k₀ := 4 * L * (16 * H + 10 * L ^ 3 * (1 + 16 * (d : ℝ) * B ^ 2))
  let c₀ := 16 * k₀ + 64 * (d : ℝ) * Y ^ 2
  let α := (d : ℝ) ^ 2 * L ^ 2 / 2
  let β₀ := 2 * (d : ℝ) * L ^ 2
  have hdNat : 0 < d := lt_of_lt_of_le (by decide : 0 < 2) (Fact.out : 2 ≤ d)
  have hd : 0 < (d : ℝ) := by exact_mod_cast hdNat
  have hk₀ : 0 < k₀ := by dsimp only [k₀]; positivity
  have hc₀ : 0 < c₀ := by dsimp only [c₀]; positivity
  have hα : 0 ≤ α := by dsimp only [α]; positivity
  have hβ₀ : 0 < β₀ := by dsimp only [β₀]; positivity
  refine ⟨4 * c₀ * (α * k₀ + β₀), by positivity, ?_⟩
  intro r₀ Q i ζ P T hP hT f g hfg t ht ρ hρ z A
  have hsqrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hr : 0 < ρ := hsqrt.trans_le hρ
  have htr : t ≤ ρ ^ 2 := by nlinarith only [Real.sq_sqrt ht.le, hρ, hsqrt]
  let u := 1 + ‖ζ‖ * Real.sqrt t
  let S := u ^ 2 / t
  have hu : 1 ≤ u := by
    dsimp only [u]
    exact le_add_of_nonneg_right (mul_nonneg (norm_nonneg ζ) hsqrt.le)
  have hS : 0 < S := by dsimp only [S]; positivity
  have h1 : t⁻¹ ≤ S := by
    dsimp only [S]
    rw [le_div_iff₀ ht]
    rw [inv_mul_cancel₀ ht.ne']
    exact one_le_pow₀ hu
  have hZ : ‖ζ‖ ^ 2 ≤ S := by
    dsimp only [S, u]
    rw [le_div_iff₀ ht]
    have he : (‖ζ‖ * Real.sqrt t) ^ 2 = ‖ζ‖ ^ 2 * t := by
      rw [mul_pow, Real.sq_sqrt ht.le]
    nlinarith only [he, mul_nonneg (norm_nonneg ζ) hsqrt.le]
  let δ := 3 * (t / 2 - t / 4) / 4
  let h := (2 * ρ - ρ) / 4
  let K := 4 * L * (H / δ / 2 + 10 * L ^ 3 *
    (‖ζ‖ ^ 2 + (d : ℝ) * B ^ 2 / h ^ 2))
  let C := 16 * K + 4 * (d : ℝ) * Y ^ 2 / h ^ 2
  have hδ : 0 < δ := by dsimp only [δ]; linarith
  have hh : 0 < h := by dsimp only [h]; linarith
  have htgap : H / δ / 2 ≤ 16 * H * S := by
    have he : H / δ / 2 = (8 * H / 3) * t⁻¹ := by
      dsimp only [δ]; field_simp; ring
    rw [he]
    have hm := mul_le_mul_of_nonneg_left h1 (show 0 ≤ 8 * H / 3 by positivity)
    exact hm.trans (mul_le_mul_of_nonneg_right (by linarith : 8 * H / 3 ≤ 16 * H) hS.le)
  have hspace : (h ^ 2)⁻¹ ≤ 16 * S := by
    have he : (h ^ 2)⁻¹ = 16 * (ρ ^ 2)⁻¹ := by
      dsimp only [h]; field_simp; ring
    rw [he]
    exact mul_le_mul_of_nonneg_left ((inv_le_inv₀ (sq_pos_of_pos hr) ht).mpr htr |>.trans h1)
      (by norm_num)
  have hK : K ≤ k₀ * S := by
    have hm := mul_le_mul_of_nonneg_left hspace (show 0 ≤ (d : ℝ) * B ^ 2 by positivity)
    have hz := add_le_add hZ hm
    dsimp only [K, k₀]
    simp only [div_eq_mul_inv] at htgap hz ⊢
    have hi := add_le_add htgap (mul_le_mul_of_nonneg_left hz (show 0 ≤ 10 * L ^ 3 by positivity))
    convert mul_le_mul_of_nonneg_left hi (show 0 ≤ 4 * L by positivity) using 1
    ring
  have hKnonneg : 0 ≤ K := by dsimp only [K]; positivity
  have hC : C ≤ c₀ * S := by
    have hm := mul_le_mul_of_nonneg_left hspace (show 0 ≤ 4 * (d : ℝ) * Y ^ 2 by positivity)
    dsimp only [C, c₀]
    simp only [div_eq_mul_inv] at hm ⊢
    nlinarith only [hK, hm]
  have hβ : α * K + β₀ * ‖ζ‖ ^ 2 ≤ (α * k₀ + β₀) * S := by
    have hm := add_le_add (mul_le_mul_of_nonneg_left hK hα)
      (mul_le_mul_of_nonneg_left hZ hβ₀.le)
    nlinarith only [hm]
  have hcoef : 4 * C * (α * K + β₀ * ‖ζ‖ ^ 2) ≤
      (4 * c₀ * (α * k₀ + β₀)) * u ^ 4 / t ^ 2 := by
    have hm := mul_le_mul (mul_le_mul_of_nonneg_left hC (by norm_num : (0 : ℝ) ≤ 4)) hβ
      (by positivity) (by positivity)
    calc
      _ ≤ (4 * (c₀ * S)) * ((α * k₀ + β₀) * S) := hm
      _ = _ := by dsimp only [S]; field_simp
  have hb := habs hP hT hfg (t / 4) (t / 2) t (by linarith) (by linarith)
    (by linarith) z ρ (2 * ρ) hr (by linarith) A
  change _ ≤ 4 * C * (α * K + β₀ * ‖ζ‖ ^ 2) * _ at hb
  change _ ≤ (4 * c₀ * (α * k₀ + β₀)) * u ^ 4 / t ^ 2 * _
  exact hb.trans (mul_le_mul_of_nonneg_right hcoef (integral_nonneg fun _ =>
    integral_nonneg fun _ => integral_nonneg fun _ => sq_nonneg _))

end C10
end EinsteinFull.Blueprint
