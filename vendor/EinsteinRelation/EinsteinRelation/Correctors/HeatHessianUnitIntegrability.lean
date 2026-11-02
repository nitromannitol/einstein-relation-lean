import EinsteinRelation.Correctors.HeatKernelMixedHessian

/-! Source: `paper/main.tex:716,748`. Unit-time Gaussian Hessian integrability. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- The unit-time heat kernel as a product of one-dimensional Gaussian factors. -/
private lemma euclideanHeatKernel_one_prod_form {d : ℕ} (x : Vec d) :
    euclideanHeatKernel (d := d) 1 x =
      (4 * Real.pi) ^ (-(d : ℝ) / 2) * ∏ k, Real.exp (-(1 / (4 : ℝ)) * x k ^ 2) := by
  have hsum : -(euclideanSq x) / (4 * 1) = ∑ k, -(1 / (4 : ℝ)) * x k ^ 2 := by
    have h1 : -(euclideanSq x) / (4 * 1) = -(1 / (4 : ℝ)) * ∑ k, x k * x k := by
      unfold euclideanSq dot; ring
    rw [h1, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring
  unfold euclideanHeatKernel
  rw [← Real.exp_sum, ← hsum]
  simp only [mul_one]

/-- Product of one-dimensional integrable factors is integrable on `Vec d`. -/
private lemma integrable_prod_coord_sol03 {d : ℕ} (g : Fin d → ℝ → ℝ)
    (hg : ∀ k, Integrable (g k)) :
    Integrable (fun x : Vec d => ∏ k, g k (x k)) volume := by
  rw [volume_pi]
  exact Integrable.fintype_prod hg

/-- `x i * x j * euclideanHeatKernel 1 x` is integrable on `Vec d`. -/
private lemma integrable_mul_mul_euclideanHeatKernel_one {d : ℕ} (i j : Fin d) :
    Integrable (fun x : Vec d => x i * x j * euclideanHeatKernel (d := d) 1 x) volume := by
  have hb : 0 < 1 / (4 : ℝ) := by norm_num
  have h_int_exp : Integrable (fun y : ℝ => Real.exp (-(1 / (4 : ℝ)) * y ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have h_int_mul : Integrable (fun y : ℝ => y * Real.exp (-(1 / (4 : ℝ)) * y ^ 2)) :=
    integrable_mul_exp_neg_mul_sq hb
  have h_int_sq : Integrable (fun y : ℝ => y ^ 2 * Real.exp (-(1 / (4 : ℝ)) * y ^ 2)) := by
    have : Integrable (fun y : ℝ => y ^ (2 : ℝ) * Real.exp (-(1 / (4 : ℝ)) * y ^ 2)) :=
      integrable_rpow_mul_exp_neg_mul_sq hb (by norm_num : (-1 : ℝ) < 2)
    simpa [Real.rpow_natCast] using this
  have hg (k : Fin d) : Integrable (fun y : ℝ => (if k = i then y else 1) *
      (if k = j then y else 1) * Real.exp (-(1 / (4 : ℝ)) * y ^ 2)) := by
    by_cases hki : k = i <;> by_cases hkj : k = j
    · simp only [if_pos hki, if_pos hkj]
      exact h_int_sq.congr (ae_of_all _ fun y => by (try dsimp only); ring)
    · simp only [if_pos hki, if_neg hkj]
      exact h_int_mul.congr (ae_of_all _ fun y => by (try dsimp only); ring)
    · simp only [if_neg hki, if_pos hkj]
      exact h_int_mul.congr (ae_of_all _ fun y => by (try dsimp only); ring)
    · simp only [if_neg hki, if_neg hkj]
      exact h_int_exp.congr (ae_of_all _ fun y => by (try dsimp only); ring)
  have hprod := integrable_prod_coord_sol03
    (fun k (y : ℝ) => (if k = i then y else 1) * (if k = j then y else 1) *
      Real.exp (-(1 / (4 : ℝ)) * y ^ 2)) hg
  have hid (x : Vec d) : (∏ k, (if k = i then x k else 1) * (if k = j then x k else 1) *
      Real.exp (-(1 / (4 : ℝ)) * x k ^ 2)) =
      x i * x j * ∏ k, Real.exp (-(1 / (4 : ℝ)) * x k ^ 2) := by
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp
  have h_eq : (fun x : Vec d => x i * x j * euclideanHeatKernel (d := d) 1 x) =
      fun x : Vec d => (4 * Real.pi) ^ (-(d : ℝ) / 2) * ∏ k, ((if k = i then x k else 1) *
        (if k = j then x k else 1) * Real.exp (-(1 / (4 : ℝ)) * x k ^ 2)) := by
    ext x
    rw [hid x, euclideanHeatKernel_one_prod_form x]
    ring
  rw [h_eq]
  exact hprod.const_mul _

/-- Every unit-time mixed Gaussian Hessian is genuinely integrable. -/
theorem integrable_unit_heatKernel_mixedHessian {d : ℕ} (i j : Fin d) :
    Integrable (coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel (d := d) 1))) volume := by
  have hfun : coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel (d := d) 1)) =
      fun x => (1 / 4 : ℝ) * (x i * x j * euclideanHeatKernel (d := d) 1 x) -
        (if i = j then (1 / 2 : ℝ) else 0) * euclideanHeatKernel (d := d) 1 x := by
    ext x
    rw [coordinateDerivative_two_euclideanHeatKernel 1 one_pos i j x]
    split_ifs <;> ring
  rw [hfun]
  exact ((integrable_mul_mul_euclideanHeatKernel_one i j).const_mul (1 / 4 : ℝ)).sub
    ((Clock.integrable_euclideanHeatKernel (d := d) one_pos).const_mul
      (if i = j then (1 / 2 : ℝ) else 0))

end EinsteinRelation.Correctors
