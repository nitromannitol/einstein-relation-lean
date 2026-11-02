import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import EinsteinFull.Frozen.LatticeConvolutionPower

open PowerSeries

namespace EinsteinFull.Blueprint

/-! # Scalar lattice renewal equations

Pure real analysis for `rt:local-mixing#fixed-radius`: the solution of a lattice renewal
equation is the convolution with the renewal sequence `U = ∑ p^{*a}`. -/

theorem lcp_eq_zero (p : ℕ → ℝ) (hp : p 0 = 0) :
    ∀ a n : ℕ, n < a → latticeConvolutionPower p a n = 0 := by
  intro a
  induction a with
  | zero => intro n h; omega
  | succ a ih =>
    intro n hn
    rw [latticeConvolutionPower]
    apply Finset.sum_eq_zero
    intro k hk
    have hkn := Finset.mem_range.mp hk
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [hp]
    · rw [ih (n - k) (by omega), mul_zero]

theorem tsum_lcp_eq_sum (p : ℕ → ℝ) (hp : p 0 = 0) (n N : ℕ) (hN : n < N) :
    (∑' a, latticeConvolutionPower p a n) =
      ∑ a ∈ Finset.range N, latticeConvolutionPower p a n :=
  tsum_eq_sum (fun a ha => lcp_eq_zero p hp a n (by
    have := Finset.mem_range.not.mp ha
    omega))

theorem U_recursion (p : ℕ → ℝ) (hp : p 0 = 0) (n : ℕ) :
    (∑' a, latticeConvolutionPower p a n) =
      (if n = 0 then 1 else 0) +
        ∑ k ∈ Finset.range (n + 1), p k * ∑' a, latticeConvolutionPower p a (n - k) := by
  rw [tsum_lcp_eq_sum p hp n (n + 2) (by omega), Finset.sum_range_succ']
  have h0 : latticeConvolutionPower p 0 n = if n = 0 then 1 else 0 := rfl
  have hstep : ∀ a : ℕ, latticeConvolutionPower p (a + 1) n =
      ∑ k ∈ Finset.range (n + 1), p k * latticeConvolutionPower p a (n - k) := fun a => rfl
  simp only [hstep, h0]
  rw [Finset.sum_comm, add_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkn := Finset.mem_range.mp hk
  rw [← Finset.mul_sum, tsum_lcp_eq_sum p hp (n - k) (n + 1) (by omega)]

theorem renewal_conv (p h r U : ℕ → ℝ)
    (hU : ∀ n, U n = (if n = 0 then 1 else 0) + ∑ k ∈ Finset.range (n + 1), p k * U (n - k))
    (hh : ∀ j, h j = r j + ∑ n ∈ Finset.range (j + 1), p n * h (j - n)) :
    ∀ j, h j = ∑ i ∈ Finset.range (j + 1), U (j - i) * r i := by
  have hU' : PowerSeries.mk U = 1 + PowerSeries.mk p * PowerSeries.mk U := by
    ext n
    simp only [map_add, coeff_mk, coeff_one, coeff_mul,
      Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact hU n
  have hh' : PowerSeries.mk h = PowerSeries.mk r + PowerSeries.mk p * PowerSeries.mk h := by
    ext n
    simp only [map_add, coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
    exact hh n
  have hu : PowerSeries.mk U * (1 - PowerSeries.mk p) = 1 := by linear_combination hU'
  have hH : PowerSeries.mk h * (1 - PowerSeries.mk p) = PowerSeries.mk r := by
    linear_combination hh'
  have h1 : PowerSeries.mk h = PowerSeries.mk r * PowerSeries.mk U := by
    calc PowerSeries.mk h = PowerSeries.mk h * (PowerSeries.mk U * (1 - PowerSeries.mk p)) := by
          rw [hu, mul_one]
      _ = (PowerSeries.mk h * (1 - PowerSeries.mk p)) * PowerSeries.mk U := by ring
      _ = PowerSeries.mk r * PowerSeries.mk U := by rw [hH]
  intro j
  have := congrArg (coeff j) h1
  simp only [coeff_mk, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk] at this
  rw [this]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end EinsteinFull.Blueprint
