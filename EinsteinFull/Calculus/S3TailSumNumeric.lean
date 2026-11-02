import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Numerical part of `p:tail#sum`

Pure real/complex-series lemmas: the double series of a product-dominated family is absolutely
summable with the product of the sums, and the resulting constants are absorbed into one
structural constant.
-/

open Filter
open scoped Topology

namespace EinsteinFull.Blueprint

theorem mul4_le {B C S Y Y' E : ℝ} (hB : B ≤ C) (hS : 0 ≤ S) (hY : Y ≤ Y') (hY0 : 0 ≤ Y)
    (hE : 0 ≤ E) (hC : 0 ≤ C) : B * S * Y * E ≤ C * S * Y' * E := by
  have h1 : B * S ≤ C * S := mul_le_mul_of_nonneg_right hB hS
  have h2 : B * S * Y ≤ C * S * Y' := mul_le_mul h1 hY hY0 (mul_nonneg hC hS)
  exact mul_le_mul_of_nonneg_right h2 hE

theorem pair_series_bound (f : ℕ × ℕ → ℂ) (a b : ℕ → ℝ) (ha0 : ∀ k, 0 ≤ a k)
    (hb0 : ∀ k, 0 ≤ b k) (hasum : Summable a) (hbsum : Summable b) (Sa Cm E : ℝ)
    (hatsum : ∑' k, a k ≤ Sa) (hbtsum : ∑' k, b k ≤ Sa) (hEnn : 0 ≤ Cm * E)
    (P1 : ∀ n m : ℕ, ‖f (n, m)‖ ≤ Cm * E * (a n * b m)) :
    Summable (fun k => ‖f k‖) ∧ (∑' k, ‖f k‖) ≤ Cm * E * (Sa * Sa) := by
  have hanorm : Summable (fun n => ‖a n‖) :=
    hasum.congr fun n => (Real.norm_of_nonneg (ha0 n)).symm
  have hbnorm : Summable (fun n => ‖b n‖) :=
    hbsum.congr fun n => (Real.norm_of_nonneg (hb0 n)).symm
  have hab : Summable (fun k : ℕ × ℕ => a k.1 * b k.2) :=
    Summable.mul_of_nonneg hasum hbsum (fun k => ha0 k) (fun k => hb0 k)
  have hpair : Summable (fun k : ℕ × ℕ => ‖f k‖) :=
    Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => P1 k.1 k.2)
      (hab.mul_left (Cm * E))
  refine ⟨hpair, ?_⟩
  calc _ ≤ ∑' k : ℕ × ℕ, Cm * E * (a k.1 * b k.2) :=
        Summable.tsum_le_tsum (fun k => P1 k.1 k.2) hpair (hab.mul_left _)
    _ = Cm * E * ((∑' n, a n) * (∑' m, b m)) := by
        rw [tsum_mul_left, tsum_mul_tsum_of_summable_norm hanorm hbnorm]
    _ ≤ Cm * E * (Sa * Sa) :=
        mul_le_mul_of_nonneg_left (mul_le_mul hatsum hbtsum (tsum_nonneg hb0)
          (le_trans (tsum_nonneg ha0) hatsum)) hEnn

theorem final_c5 {B C Ca cm sL S2 Z S : ℝ} (hBC : B ≤ C) (hS2 : 0 ≤ S2) (hCpos : 0 ≤ C)
    (hexp2 : Real.exp (2 * Ca * sL) * Real.exp (2 * cm) ≤ Real.exp (C * sL))
    (hS : S ≤ B * S2 * Real.exp (2 * Ca * sL) * (Real.exp (-Z) * Real.exp (2 * cm))) :
    S ≤ C * S2 * (Real.exp (C * sL) * Real.exp (-Z)) := by
  calc S ≤ B * S2 * Real.exp (2 * Ca * sL) * (Real.exp (-Z) * Real.exp (2 * cm)) := hS
    _ = B * S2 * (Real.exp (2 * Ca * sL) * Real.exp (2 * cm)) * Real.exp (-Z) := by ring
    _ ≤ C * S2 * Real.exp (C * sL) * Real.exp (-Z) :=
        mul4_le hBC hS2 hexp2 (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
          (Real.exp_pos _).le hCpos
    _ = C * S2 * (Real.exp (C * sL) * Real.exp (-Z)) := by ring

theorem tail_sum_bounds (d : ℕ) (S Kn Cm Ca cm C l s h L X Z Sa : ℝ)
    (hl : 0 < l) (hCm : 0 < Cm) (hcm : 0 < cm) (hCa : 0 < Ca) (hs : 0 < s)
    (hL1 : 1 ≤ Real.sqrt L) (hh2 : 2 * h = (d : ℝ) + 2)
    (hC1 : Cm * Ca ^ 2 + 2 * Ca + 2 * cm + Cm + Cm * l ≤ C)
    (hXe : -X = -Z + 2 * cm) (hSa : Sa = Ca * s ^ h * Real.exp (Ca * Real.sqrt L))
    (hKS : Kn ≤ S) (hS : S ≤ Cm * Real.exp (-X) * (Sa * Sa)) :
    S ≤ C * s ^ (2 * h) * Real.exp (C * Real.sqrt L - X) ∧
      Kn ≤ C * s ^ (d + 2) * Real.exp (C * Real.sqrt L - Z) := by
  have hp1 : 0 < Cm * l := mul_pos hCm hl
  have hp2 : 0 ≤ Cm * Ca ^ 2 := mul_nonneg hCm.le (sq_nonneg Ca)
  have hCpos : 0 ≤ C := by linarith
  have hBC : Cm * Ca ^ 2 ≤ C := by linarith
  have h2CaC : 2 * Ca ≤ C := by linarith
  have h2CaCm : 2 * Ca + 2 * cm ≤ C := by linarith
  have hS2 : 0 ≤ s ^ (2 * h) := Real.rpow_nonneg hs.le _
  have hSS : Sa * Sa = Ca ^ 2 * s ^ (2 * h) * Real.exp (2 * Ca * Real.sqrt L) := by
    have e1 : s ^ h * s ^ h = s ^ (2 * h) := by
      rw [← Real.rpow_add hs]; congr 1; ring
    have e2 : Real.exp (Ca * Real.sqrt L) * Real.exp (Ca * Real.sqrt L) =
        Real.exp (2 * Ca * Real.sqrt L) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [hSa]
    calc _ = Ca ^ 2 * (s ^ h * s ^ h) *
          (Real.exp (Ca * Real.sqrt L) * Real.exp (Ca * Real.sqrt L)) := by ring
      _ = _ := by rw [e1, e2]
  have hsum2 : S ≤ (Cm * Ca ^ 2) * s ^ (2 * h) * Real.exp (2 * Ca * Real.sqrt L) *
      Real.exp (-X) := by
    refine hS.trans (le_of_eq ?_)
    rw [hSS]; ring
  have hexp1 : Real.exp (2 * Ca * Real.sqrt L) ≤ Real.exp (C * Real.sqrt L) := by
    apply Real.exp_le_exp.2
    have := mul_le_mul_of_nonneg_right h2CaC (Real.sqrt_nonneg L)
    linarith
  refine ⟨?_, ?_⟩
  · refine hsum2.trans ?_
    have e : C * s ^ (2 * h) * Real.exp (C * Real.sqrt L - X) =
        C * s ^ (2 * h) * Real.exp (C * Real.sqrt L) * Real.exp (-X) := by
      rw [sub_eq_add_neg, Real.exp_add]; ring
    rw [e]
    exact mul4_le hBC hS2 hexp1 (Real.exp_pos _).le (Real.exp_pos _).le hCpos
  · have hpow : s ^ (2 * h) = s ^ (d + 2) := by
      rw [hh2, show ((d : ℝ) + 2) = ((d + 2 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
    have hexp2 : Real.exp (2 * Ca * Real.sqrt L) * Real.exp (2 * cm) ≤
        Real.exp (C * Real.sqrt L) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.2
      have h1 : (2 * Ca + 2 * cm) * Real.sqrt L ≤ C * Real.sqrt L :=
        mul_le_mul_of_nonneg_right h2CaCm (Real.sqrt_nonneg L)
      have h2 : 2 * cm ≤ 2 * cm * Real.sqrt L :=
        le_mul_of_one_le_right (by positivity) hL1
      linarith
    have h5 : Kn ≤ (Cm * Ca ^ 2) * s ^ (d + 2) * Real.exp (2 * Ca * Real.sqrt L) *
        (Real.exp (-Z) * Real.exp (2 * cm)) := by
      refine hKS.trans (hsum2.trans (le_of_eq ?_))
      rw [hXe, Real.exp_add, hpow]
    have h6 := final_c5 hBC (pow_nonneg hs.le (d + 2)) hCpos hexp2 h5
    have e : C * s ^ (d + 2) * Real.exp (C * Real.sqrt L - Z) =
        C * s ^ (d + 2) * (Real.exp (C * Real.sqrt L) * Real.exp (-Z)) := by
      rw [sub_eq_add_neg, Real.exp_add]
    rw [e]
    exact h6

end EinsteinFull.Blueprint
