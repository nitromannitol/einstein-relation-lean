import EinsteinRelation.Correctors.HeatKernelMixedHessian
import EinsteinRelation.Correctors.HeatKernelConvolution

/-!
# Pointwise bounds for the Hessian of the heat kernel

The mixed second derivatives of the Euclidean heat kernel `Φ_t(x) = (4πt)^(-d/2) e^(-|x|²/(4t))`
are bounded by a multiple of `t⁻¹ Φ_{2t}(x)`: `|∂ᵢ∂ⱼ Φ_t(x)| ≤ 2^(d/2) (2/t) Φ_{2t}(x)`. This is the
form in which the heat formula (6.7) of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, is estimated: integrability and tails of the
Hessian reduce to those of a Gaussian of doubled variance.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors

variable {d : ℕ}

theorem abs_mul_le_euclideanSq (x : Vec d) (i j : Fin d) : |x i * x j| ≤ euclideanSq x := by
  have hsum : ∀ k : Fin d, x k ^ 2 ≤ euclideanSq x := fun k => by
    have h := Finset.single_le_sum (f := fun l => x l * x l) (fun l _ => mul_self_nonneg (x l))
      (Finset.mem_univ k)
    simpa [euclideanSq, dot, sq] using h
  by_cases hij : i = j
  · subst hij
    rw [abs_mul_self, ← sq]
    exact hsum i
  · have hpair : x i ^ 2 + x j ^ 2 ≤ euclideanSq x := by
      have h := Finset.sum_le_sum_of_subset_of_nonneg (f := fun l => x l * x l)
        (Finset.subset_univ {i, j}) (fun l _ _ => mul_self_nonneg (x l))
      rw [Finset.sum_pair hij] at h
      simpa [euclideanSq, dot, sq] using h
    rw [abs_mul]
    nlinarith [sq_abs (x i), sq_abs (x j), sq_nonneg (|x i| - |x j|)]

theorem two_mul_le_exp {u : ℝ} (hu : 0 ≤ u) : 2 * u ≤ Real.exp u := by
  have h := Real.quadratic_le_exp_of_nonneg hu
  nlinarith [sq_nonneg (u - 1)]

/-- The heat kernel at time `t` is `2^(d/2) e^(-|x|²/(8t))` times the heat kernel at time `2t`. -/
theorem euclideanHeatKernel_eq_two_mul {t : ℝ} (ht : 0 < t) (x : Vec d) :
    euclideanHeatKernel t x =
      (2 : ℝ) ^ ((d : ℝ) / 2) * Real.exp (-euclideanSq x / (8 * t)) *
        euclideanHeatKernel (2 * t) x := by
  have hp : (4 * Real.pi * (2 * t)) ^ (-(d : ℝ) / 2) =
      (2 : ℝ) ^ (-(d : ℝ) / 2) * (4 * Real.pi * t) ^ (-(d : ℝ) / 2) := by
    rw [show 4 * Real.pi * (2 * t) = 2 * (4 * Real.pi * t) by ring,
      Real.mul_rpow (by norm_num) (by positivity)]
  have htwo : (2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ) / 2) = 1 := by
    rw [← Real.rpow_add (by norm_num), show (d : ℝ) / 2 + -(d : ℝ) / 2 = 0 by ring,
      Real.rpow_zero]
  unfold euclideanHeatKernel
  rw [hp, show -euclideanSq x / (4 * t) =
      -euclideanSq x / (8 * t) + -euclideanSq x / (4 * (2 * t)) by ring,
    Real.exp_add]
  calc (4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
        (Real.exp (-euclideanSq x / (8 * t)) * Real.exp (-euclideanSq x / (4 * (2 * t))))
      = ((2 : ℝ) ^ ((d : ℝ) / 2) * (2 : ℝ) ^ (-(d : ℝ) / 2)) *
        ((4 * Real.pi * t) ^ (-(d : ℝ) / 2) *
          (Real.exp (-euclideanSq x / (8 * t)) *
            Real.exp (-euclideanSq x / (4 * (2 * t))))) := by rw [htwo, one_mul]
    _ = _ := by ring

/-- **Gaussian bound for the heat-kernel Hessian.** -/
theorem abs_heatHessian_le {t : ℝ} (ht : 0 < t) (i j : Fin d) (x : Vec d) :
    |coordinateDerivative j (coordinateDerivative i (euclideanHeatKernel t)) x| ≤
      (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t) * euclideanHeatKernel (2 * t) x := by
  rw [coordinateDerivative_two_euclideanHeatKernel t ht i j x,
    euclideanHeatKernel_eq_two_mul ht x]
  have ht0 : t ≠ 0 := ht.ne'
  set u := euclideanSq x / (8 * t) with hu
  have hx0 : 0 ≤ euclideanSq x := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun l _ => mul_self_nonneg (x l)
  have hu0 : 0 ≤ u := by positivity
  have hexp : Real.exp (-euclideanSq x / (8 * t)) = (Real.exp u)⁻¹ := by
    rw [← Real.exp_neg, hu, neg_div]
  have hE : 0 < Real.exp u := Real.exp_pos u
  have h2u := two_mul_le_exp hu0
  have hc : 0 ≤ (2 : ℝ) ^ ((d : ℝ) / 2) := by positivity
  have hK : 0 ≤ euclideanHeatKernel (2 * t) x := euclideanHeatKernel_nonneg (by positivity) x
  have hxx := abs_mul_le_euclideanSq x i j
  have hsq : euclideanSq x = 8 * t * u := by
    rw [hu]
    field_simp
  have hbrack : |x i * x j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)| ≤
      (2 * u + 1 / 2) / t := by
    have h1 : |x i * x j / (4 * t ^ 2)| ≤ 2 * u / t := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 4 * t ^ 2), div_le_div_iff₀
        (by positivity) ht]
      rw [hsq] at hxx
      nlinarith
    have h2 : |(if i = j then 1 / (2 * t) else 0)| ≤ 1 / 2 / t := by
      split_ifs
      · rw [abs_of_pos (by positivity)]
        exact le_of_eq (by ring)
      · rw [abs_zero]
        positivity
    calc _ ≤ |x i * x j / (4 * t ^ 2)| + |(if i = j then 1 / (2 * t) else 0)| := abs_sub _ _
      _ ≤ 2 * u / t + 1 / 2 / t := add_le_add h1 h2
      _ = (2 * u + 1 / 2) / t := by ring
  rw [hexp, abs_mul, abs_of_nonneg (by positivity)]
  calc (2 : ℝ) ^ ((d : ℝ) / 2) * (Real.exp u)⁻¹ * euclideanHeatKernel (2 * t) x *
        |x i * x j / (4 * t ^ 2) - (if i = j then 1 / (2 * t) else 0)|
      ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * (Real.exp u)⁻¹ * euclideanHeatKernel (2 * t) x *
        ((2 * u + 1 / 2) / t) := by gcongr
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * t) x *
        ((2 * u + 1 / 2) / Real.exp u) / t := by
        ring
    _ ≤ (2 : ℝ) ^ ((d : ℝ) / 2) * euclideanHeatKernel (2 * t) x * 2 / t := by
        gcongr
        rw [div_le_iff₀ hE]
        have : 1 ≤ Real.exp u := Real.one_le_exp hu0
        linarith
    _ = (2 : ℝ) ^ ((d : ℝ) / 2) * (2 / t) * euclideanHeatKernel (2 * t) x := by ring

end EinsteinFull.Homogenization
