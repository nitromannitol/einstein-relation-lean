import EinsteinFull.Homogenization.HeatGradientWindow
import EinsteinFull.Homogenization.HeatHessianL2

/-!
# Gaussian bounds for the gradients of heat-kernel derivatives

The third derivatives of the heat kernel satisfy `|∂ₗ∂ⱼ∂ᵢΦ_t| ≤ 2^(d/2) (10 / (t √t)) Φ_{2t}`, so
the Euclidean norm of the gradient of the mixed Hessian `∂ⱼ∂ᵢΦ_t` is at most `√d` times this
bound; the gradient of `∂ᵢΦ_t` is bounded by `√d 2^(d/2) (2/t) Φ_{2t}`. These are the bounds on
the Gaussian tests of the heat formula (6.7) of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, when they are paired with fields of small
negative Sobolev norm.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors

variable {d : ℕ}

theorem sum_mul_unitVector (z : Vec d) (l : Fin d) : ∑ k, z k * unitVector l k = z l := by
  simp [unitVector, Pi.single_apply]

/-- The third derivatives of the heat kernel. -/
theorem coordinateDerivative_heatHessianKernel (t : ℝ) (i j l : Fin d) (z : Vec d) :
    coordinateDerivative l (heatHessianKernel t i j) z =
      euclideanHeatKernel t z *
        (-(1 / (2 * t)) * z l * (z i * z j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) +
          ((if j = l then z i else 0) + (if i = l then z j else 0)) / (4 * t ^ 2)) := by
  have hΦ := ((contDiff_euclideanHeatKernel (d := d) t).differentiable (by simp) z).hasFDerivAt
  have hp := (((hasFDerivAt_apply (𝕜 := ℝ) i z).mul (hasFDerivAt_apply (𝕜 := ℝ) j z)).const_mul
    (4 * t ^ 2)⁻¹).sub_const (if i = j then 1 / (2 * t) else 0)
  have h := (hΦ.mul hp).congr_of_eventuallyEq (f₁ := heatHessianKernel (d := d) t i j)
    (Filter.Eventually.of_forall fun y => by
      simp only [heatHessianKernel, Pi.mul_apply]
      ring)
  unfold coordinateDerivative
  rw [h.fderiv]
  simp only [FunLike.coe_add, FunLike.coe_smul, Pi.add_apply,
    Pi.smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  rw [fderiv_euclideanHeatKernel t z (unitVector l), sum_mul_unitVector]
  simp only [unitVector, Pi.single_apply]
  by_cases hjl : j = l <;> by_cases hil : i = l <;> simp [hjl, hil] <;> ring

theorem euclideanNorm_le_sqrt_mul_of_abs_le {v : Vec d} {M : ℝ} (h : ∀ l, |v l| ≤ M) :
    euclideanNorm v ≤ Real.sqrt d * M := by
  rcases Nat.eq_zero_or_pos d with hd | hd
  · subst hd
    simp [euclideanNorm, euclideanSq, dot]
  have hM : 0 ≤ M := (abs_nonneg _).trans (h ⟨0, hd⟩)
  have hsq : euclideanSq v ≤ d * M ^ 2 := by
    unfold euclideanSq dot
    calc ∑ l, v l * v l ≤ ∑ _l : Fin d, M ^ 2 := Finset.sum_le_sum fun l _ => by
          have := h l
          nlinarith [abs_nonneg (v l), sq_abs (v l)]
      _ = d * M ^ 2 := by simp
  calc euclideanNorm v ≤ Real.sqrt (d * M ^ 2) := Real.sqrt_le_sqrt hsq
    _ = Real.sqrt d * M := by
        rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hM]

theorem mul_exp_neg_le_ten (w : ℝ) :
    (w ^ 3 / 8 + 3 * w / 4) * Real.exp (-(w ^ 2 / 8)) ≤ 10 := by
  have hv : 0 ≤ w ^ 2 / 8 := by positivity
  have he := Real.quadratic_le_exp_of_nonneg hv
  have hE : 0 < Real.exp (w ^ 2 / 8) := Real.exp_pos _
  rw [Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ hE]
  nlinarith [sq_nonneg (w ^ 2 - w), sq_nonneg (w - 1), sq_nonneg w]

/-- **Gaussian bound for the third derivatives of the heat kernel.** -/
theorem abs_coordinateDerivative_heatHessian_le {t : ℝ} (ht : 0 < t) (i j l : Fin d)
    (z : Vec d) :
    |coordinateDerivative l (coordinateDerivative j (coordinateDerivative i
        (euclideanHeatKernel t))) z| ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * (10 / (t * Real.sqrt t)) * euclideanHeatKernel (2 * t) z := by
  rw [heatHessian_eq ht]
  change |coordinateDerivative l (heatHessianKernel t i j) z| ≤ _
  rw [coordinateDerivative_heatHessianKernel, euclideanHeatKernel_eq_two_mul ht z]
  set s := Real.sqrt t with hs
  have hs0 : 0 < s := Real.sqrt_pos.mpr ht
  have hst : s ^ 2 = t := Real.sq_sqrt ht.le
  set N := euclideanNorm z with hN
  have hN0 : 0 ≤ N := by rw [hN]; unfold euclideanNorm; positivity
  have hsq : euclideanSq z = N ^ 2 := euclideanSq_eq_euclideanNorm_sq z
  have hzl : |z l| ≤ N := abs_apply_le_euclideanNorm z l
  have hzi : |z i| ≤ N := abs_apply_le_euclideanNorm z i
  have hzj : |z j| ≤ N := abs_apply_le_euclideanNorm z j
  have hzij : |z i * z j| ≤ N ^ 2 := by rw [← hsq]; exact abs_mul_le_euclideanSq z i j
  have hK : 0 ≤ euclideanHeatKernel (2 * t) z := euclideanHeatKernel_nonneg (by positivity) z
  have hc : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := by positivity
  have hp : |z i * z j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| ≤
      N ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
    have h1 : |z i * z j / (4 * t ^ 2)| ≤ N ^ 2 / (4 * t ^ 2) := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * t ^ 2)]
      gcongr
    have h2 : |(if i = j then 1 / (2 * t) else 0)| ≤ 1 / (2 * t) := by
      split_ifs
      · rw [abs_of_pos (by positivity)]
      · rw [abs_zero]
        positivity
    exact (abs_sub _ _).trans (add_le_add h1 h2)
  have hq : |(if j = l then z i else 0) + (if i = l then z j else 0)| ≤ 2 * N := by
    have h1 : |(if j = l then z i else 0)| ≤ N := by
      split_ifs
      · exact hzi
      · rw [abs_zero]; exact hN0
    have h2 : |(if i = l then z j else 0)| ≤ N := by
      split_ifs
      · exact hzj
      · rw [abs_zero]; exact hN0
    linarith [abs_add_le (if j = l then z i else 0) (if i = l then z j else 0)]
  have hbr : |-(1 / (2 * t)) * z l * (z i * z j / (4 * t ^ 2) -
        (if i = j then 1 / (2 * t) else 0)) +
      ((if j = l then z i else 0) + (if i = l then z j else 0)) / (4 * t ^ 2)| ≤
      N / (2 * t) * (N ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) + 2 * N / (4 * t ^ 2) := by
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * t))]
      calc 1 / (2 * t) * |z l| * |z i * z j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)|
          ≤ 1 / (2 * t) * N * (N ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) := by gcongr
        _ = N / (2 * t) * (N ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) := by ring
    · rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * t ^ 2)]
      gcongr
  set w := N / s with hw
  have hNw : N = w * s := by rw [hw]; field_simp
  have hw0 : 0 ≤ w := by positivity
  have hexp : Real.exp (-euclideanSq z / (8 * t)) = Real.exp (-(w ^ 2 / 8)) := by
    congr 1
    rw [hsq, hNw, ← hst]
    field_simp
  have hbr' : N / (2 * t) * (N ^ 2 / (4 * t ^ 2) + 1 / (2 * t)) + 2 * N / (4 * t ^ 2) =
      (w ^ 3 / 8 + 3 * w / 4) / (t * s) := by
    rw [hNw, ← hst]
    field_simp
    ring
  rw [hexp, abs_mul, abs_of_nonneg (by positivity)]
  have hE := mul_exp_neg_le_ten w
  calc (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(w ^ 2 / 8)) * euclideanHeatKernel (2 * t) z *
        |-(1 / (2 * t)) * z l * (z i * z j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)) +
          ((if j = l then z i else 0) + (if i = l then z j else 0)) / (4 * t ^ 2)|
      ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-(w ^ 2 / 8)) * euclideanHeatKernel (2 * t) z *
        ((w ^ 3 / 8 + 3 * w / 4) / (t * s)) := by
        rw [← hbr']
        gcongr
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) * ((w ^ 3 / 8 + 3 * w / 4) * Real.exp (-(w ^ 2 / 8))) /
          (t * s) * euclideanHeatKernel (2 * t) z := by ring
    _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * 10 / (t * s) * euclideanHeatKernel (2 * t) z := by
        gcongr
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) * (10 / (t * s)) * euclideanHeatKernel (2 * t) z := by ring

/-- **Gaussian bound for the gradient of the heat-kernel Hessian.** -/
theorem euclideanNorm_gradient_heatHessian_le {t : ℝ} (ht : 0 < t) (i j : Fin d) (z : Vec d) :
    euclideanNorm (gradient (coordinateDerivative j (coordinateDerivative i
        (euclideanHeatKernel t))) z) ≤
      Real.sqrt d * ((2 : ℝ) ^ ((d : ℝ) / 2) * (10 / (t * Real.sqrt t))) *
        euclideanHeatKernel (2 * t) z := by
  rw [mul_assoc]
  exact euclideanNorm_le_sqrt_mul_of_abs_le fun l =>
    abs_coordinateDerivative_heatHessian_le ht i j l z

/-- **Gaussian bound for the gradient of the heat-kernel gradient.** -/
theorem euclideanNorm_gradient_heatGrad_le {t : ℝ} (ht : 0 < t) (i : Fin d) (z : Vec d) :
    euclideanNorm (gradient (coordinateDerivative i (euclideanHeatKernel t)) z) ≤
      Real.sqrt d * ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t)) * euclideanHeatKernel (2 * t) z := by
  rw [mul_assoc]
  exact euclideanNorm_le_sqrt_mul_of_abs_le fun l => abs_heatHessian_le ht i l z

/-- The Hessian of the heat kernel is smooth. -/
theorem contDiff_heatHessian (t : ℝ) (i j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j (coordinateDerivative i
      (euclideanHeatKernel (d := d) t))) :=
  contDiff_coordinateDerivative (contDiff_coordinateDerivative
    (contDiff_euclideanHeatKernel t) i) j

/-- The gradient of the heat kernel is smooth. -/
theorem contDiff_heatGrad (t : ℝ) (i : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative i (euclideanHeatKernel (d := d) t)) :=
  contDiff_coordinateDerivative (contDiff_euclideanHeatKernel t) i

end EinsteinFull.Homogenization
