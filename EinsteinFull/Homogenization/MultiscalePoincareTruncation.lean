import EinsteinFull.Homogenization.NegativeBesovTruncation
import Homogenization.Book.Ch01.Theorems.MultiscalePoincare

/-!
# Finite-scale multiscale Poincaré inequality

A cube function's oscillation is controlled by averaged gradients at a finite
family of scales and the `L²` norm of its gradient. This is the multiscale
Poincaré argument of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Corollary 1.14.
-/

open scoped ENNReal
open _root_.Homogenization

namespace EinsteinFull.Homogenization

/-- A finite-scale multiscale Poincaré bound, with the small-scale remainder
expressed through the normalized cube `L²` norms of the gradient coordinates. -/
theorem cubeBesovOscillation_le_sum_scales_add_tail
    {d : ℕ} [NeZero d] (Q : TriadicCube d) (u : H1Function (openCubeSet Q)) (N : ℕ) :
    cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u x) ≤
      (Book.Ch01.Legacy.fullVectorPoincareConstant Q * (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ∑ i : Fin d,
        ((∑ j ∈ Finset.range N, cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞)
          (fun x => u.grad x i) j) +
        (cubeBesovScaleWeight (-1) Q * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.grad x i)) *
          ((1 / 3 : ℝ) ^ N / (1 - 1 / 3))) := by
  let C : ℝ := Book.Ch01.Legacy.fullVectorPoincareConstant Q
  let D : ℝ := (3 : ℝ) ^ ((d : ℝ) + 1)
  have hC : 0 ≤ C := Book.Ch01.Legacy.fullVectorPoincareConstant_nonneg Q
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hdual := Book.Ch01.Legacy.h1_fullVectorPoincare Q u
  change cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u x) ≤
    C * ∑ i : Fin d, cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) 1
      (fun x => u.grad x i) at hdual
  have hconj : cubeBesovConjExponent (2 : ℝ≥0∞) = (2 : ℝ≥0∞) := by
    simpa [cubeBesovConjExponent] using
      (ENNReal.HolderConjugate.conjExponent_eq (p := (2 : ℝ≥0∞)) (q := (2 : ℝ≥0∞)))
  have hcoord (i : Fin d) : cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) 1
      (fun x => u.grad x i) ≤ D * cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) 1
        (fun x => u.grad x i) := by
    simpa [D] using cubeBesovDualFullNorm_le_note_constant_mul_cubeBesovCircNorm
      (Q := Q) (s := 1) (p := (2 : ℝ≥0∞)) (q := (1 : ℝ≥0∞))
      (u := fun x => u.grad x i) (by norm_num) (u.grad_coord_memL2_normalizedCubeMeasure i)
      (by norm_num) (by norm_num) (by intro htop; simp [hconj] at htop) (by norm_num)
  calc
    _ ≤ C * ∑ i : Fin d, cubeBesovDualFullNorm Q 1 (2 : ℝ≥0∞) 1
          (fun x => u.grad x i) := hdual
    _ ≤ C * ∑ i : Fin d, D * cubeBesovCircNorm Q 1 (2 : ℝ≥0∞) 1
          (fun x => u.grad x i) := by
      exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hcoord i)) hC
    _ ≤ C * ∑ i : Fin d, D *
        ((∑ j ∈ Finset.range N, cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞)
          (fun x => u.grad x i) j) +
        (cubeBesovScaleWeight (-1) Q * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.grad x i)) *
          ((1 / 3 : ℝ) ^ N / (1 - 1 / 3))) := by
      apply mul_le_mul_of_nonneg_left _ hC
      apply Finset.sum_le_sum
      intro i _
      exact mul_le_mul_of_nonneg_left
        (cubeBesovCircNorm_one_two_le_scales_add_tail Q _ N
          (u.grad_coord_memL2_normalizedCubeMeasure i)) hD
    _ = _ := by rw [← Finset.mul_sum]; ring

/-- On a cube of side `3 ^ n`, truncation below unit scale leaves a remainder
of one half of the normalized `L²` norm in each coordinate. -/
theorem originCubeBesovOscillation_le_sum_scales_add_gradient
    {d : ℕ} [NeZero d] (n : ℕ)
    (u : H1Function (openCubeSet (originCube d (n : ℤ)))) :
    cubeBesovOscillation (originCube d (n : ℤ)) (2 : ℝ≥0∞) (fun x => u x) ≤
      (Book.Ch01.Legacy.fullVectorPoincareConstant (originCube d (n : ℤ)) *
        (3 : ℝ) ^ ((d : ℝ) + 1)) *
      ∑ i : Fin d,
        ((∑ j ∈ Finset.range (n + 1),
          cubeBesovCircDepthSeminorm (originCube d (n : ℤ)) 1 (2 : ℝ≥0∞)
            (fun x => u.grad x i) j) +
        (1 / 2 : ℝ) * cubeLpNorm (originCube d (n : ℤ)) (2 : ℝ≥0∞)
          (fun x => u.grad x i)) := by
  let Q := originCube d (n : ℤ)
  have hscale : cubeBesovScaleWeight (-1) Q *
      ((1 / 3 : ℝ) ^ (n + 1) / (1 - 1 / 3)) = 1 / 2 := by
    simp only [Q, cubeBesovScaleWeight, neg_neg, cubeScaleFactor_originCube, Real.rpow_one,
      zpow_natCast, pow_succ]
    have hp : (3 : ℝ) ^ n ≠ 0 := pow_ne_zero _ (by norm_num)
    have he : (1 / 3 : ℝ) ^ n = ((3 : ℝ) ^ n)⁻¹ := by rw [one_div, inv_pow]
    rw [he]
    field_simp
    norm_num
  have h := cubeBesovOscillation_le_sum_scales_add_tail Q u (n + 1)
  refine h.trans_eq ?_
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  have htail : (cubeBesovScaleWeight (-1) Q * cubeLpNorm Q (2 : ℝ≥0∞)
      (fun x => u.grad x i)) * ((1 / 3 : ℝ) ^ (n + 1) / (1 - 1 / 3)) =
      (1 / 2 : ℝ) * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.grad x i) := by
    calc
      _ = (cubeBesovScaleWeight (-1) Q * ((1 / 3 : ℝ) ^ (n + 1) / (1 - 1 / 3))) *
          cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.grad x i) := by ring
      _ = _ := by rw [hscale]
  rw [htail]

end EinsteinFull.Homogenization
