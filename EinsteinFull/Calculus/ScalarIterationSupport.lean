import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Algebra.Order.Field.GeomSum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Coupled scalar iteration

The averaged majorant `K` and pointwise majorant `P` preserve `P ≤ 2 * c * K`.
Their error increments give an exponential bound in the partial sum of errors.
Geometric and dyadic errors give constants uniform in the iteration length.
All recurrence premises are restricted to a finite prefix, allowing iteration
up to a terminal admissible time.
-/

namespace EinsteinFull

/-- One coupled step preserves the pointwise-to-averaged ratio. -/
theorem coupled_iteration_step (c K P e : ℝ) (hc : 0 ≤ c) (hP : 0 ≤ P)
    (he : 0 ≤ e) (hbound : P ≤ 2 * c * K) :
    K ≤ K + e * P ∧
    K + e * P ≤ (1 + 2 * c * e) * K ∧
    max P (c * (K + e * P) + P / 2) ≤ 2 * c * (K + e * P) := by
  have hmono : K ≤ K + e * P := le_add_of_nonneg_right (mul_nonneg he hP)
  have hbound' : P ≤ 2 * c * (K + e * P) :=
    hbound.trans (mul_le_mul_of_nonneg_left hmono (mul_nonneg (by norm_num) hc))
  refine ⟨hmono, ?_, max_le hbound' ?_⟩
  · have h := mul_le_mul_of_nonneg_left hbound he
    nlinarith only [h]
  · linarith only [hbound']

/-- The initialized ratio is invariant under the coupled majorant recurrences. -/
theorem coupled_iteration_invariant (c : ℝ) (hc : 0 ≤ c)
    (K P e : ℕ → ℝ) (N : ℕ)
    (hP : ∀ n, n < N → 0 ≤ P n) (he : ∀ n, n < N → 0 ≤ e n)
    (hinit : P 0 ≤ 2 * c * K 0)
    (hK : ∀ n, n < N → K (n + 1) = K n + e n * P n)
    (hstep : ∀ n, n < N → P (n + 1) ≤ max (P n) (c * K (n + 1) + P n / 2))
    (n : ℕ) : n ≤ N → P n ≤ 2 * c * K n := by
  induction n with
  | zero => intro _; exact hinit
  | succ n ih =>
    intro hn
    have hlt : n < N := lt_of_lt_of_le (Nat.lt_succ_self n) hn
    have h := (coupled_iteration_step c (K n) (P n) (e n)
      hc (hP n hlt) (he n hlt) (ih hlt.le)).2.2
    rw [← hK n hlt] at h
    exact (hstep n hlt).trans h

/-- A summable error produces an exponential bound, with no smallness premise. -/
theorem coupled_iteration_le_exp_sum (c : ℝ) (hc : 0 ≤ c)
    (K P e : ℕ → ℝ) (N : ℕ) (hK0 : 0 ≤ K 0)
    (hP : ∀ n, n < N → 0 ≤ P n) (he : ∀ n, n < N → 0 ≤ e n)
    (hinit : P 0 ≤ 2 * c * K 0)
    (hK : ∀ n, n < N → K (n + 1) = K n + e n * P n)
    (hstep : ∀ n, n < N → P (n + 1) ≤ max (P n) (c * K (n + 1) + P n / 2))
    (n : ℕ) : n ≤ N →
    K n ≤ K 0 * Real.exp (2 * c * ∑ i ∈ Finset.range n, e i) := by
  induction n with
  | zero =>
    intro _
    simp only [Finset.range_zero, Finset.sum_empty, mul_zero, Real.exp_zero, mul_one,
      le_refl]
  | succ n ih =>
    intro hn
    have hlt : n < N := lt_of_lt_of_le (Nat.lt_succ_self n) hn
    have hratio := coupled_iteration_invariant c hc K P e N hP he hinit hK hstep n hlt.le
    have hlocal := (coupled_iteration_step c (K n) (P n) (e n)
      hc (hP n hlt) (he n hlt) hratio).2.1
    have hcoef : 0 ≤ 2 * c * e n := mul_nonneg (mul_nonneg (by norm_num) hc) (he n hlt)
    have hexp : 1 + 2 * c * e n ≤ Real.exp (2 * c * e n) := by
      simpa only [add_comm] using Real.add_one_le_exp (2 * c * e n)
    rw [hK n hlt]
    calc
      K n + e n * P n ≤ (1 + 2 * c * e n) * K n := hlocal
      _ ≤ (1 + 2 * c * e n) *
          (K 0 * Real.exp (2 * c * ∑ i ∈ Finset.range n, e i)) :=
        mul_le_mul_of_nonneg_left (ih hlt.le) (by linarith only [hcoef])
      _ ≤ Real.exp (2 * c * e n) *
          (K 0 * Real.exp (2 * c * ∑ i ∈ Finset.range n, e i)) :=
        mul_le_mul_of_nonneg_right hexp (mul_nonneg hK0 (Real.exp_pos _).le)
      _ = K 0 * Real.exp (2 * c * ∑ i ∈ Finset.range (n + 1), e i) := by
        rw [Finset.sum_range_succ, mul_add, Real.exp_add]
        ring

/-- Geometrically decaying dyadic errors give bounds uniform in the number of steps. -/
theorem coupled_iteration_le_geometric_exp (c A q : ℝ) (hc : 0 ≤ c)
    (hA : 0 ≤ A) (hq : 0 ≤ q) (hq1 : q < 1)
    (K P : ℕ → ℝ) (N : ℕ) (hK0 : 0 ≤ K 0) (hP : ∀ n, n < N → 0 ≤ P n)
    (hinit : P 0 ≤ 2 * c * K 0)
    (hK : ∀ n, n < N → K (n + 1) = K n + (A * q ^ n) * P n)
    (hstep : ∀ n, n < N → P (n + 1) ≤ max (P n) (c * K (n + 1) + P n / 2))
    (n : ℕ) (hn : n ≤ N) :
    K n ≤ K 0 * Real.exp (2 * c * A / (1 - q)) ∧
    P n ≤ 2 * c * (K 0 * Real.exp (2 * c * A / (1 - q))) := by
  have he : ∀ i : ℕ, 0 ≤ A * q ^ i := fun i => mul_nonneg hA (pow_nonneg hq i)
  have hgeom : (∑ i ∈ Finset.range n, q ^ i) ≤ 1 / (1 - q) := by
    simpa only [Nat.Ico_zero_eq_range, pow_zero] using
      (geom_sum_Ico_le_of_lt_one hq hq1 (m := 0) (n := n))
  have hsum : (∑ i ∈ Finset.range n, A * q ^ i) ≤ A / (1 - q) := by
    rw [← Finset.mul_sum]
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hgeom hA
  have hbound : K n ≤ K 0 * Real.exp (2 * c * A / (1 - q)) := by
    refine (coupled_iteration_le_exp_sum c hc K P (fun i => A * q ^ i) N
      hK0 hP (fun i _ => he i) hinit hK hstep n hn).trans ?_
    apply mul_le_mul_of_nonneg_left _ hK0
    apply Real.exp_le_exp.mpr
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num) hc)
  exact ⟨hbound, (coupled_iteration_invariant c hc K P (fun i => A * q ^ i) N
    hP (fun i _ => he i) hinit hK hstep n hn).trans
      (mul_le_mul_of_nonneg_left hbound (mul_nonneg (by norm_num) hc))⟩

/-- The scalar bootstrap's dyadic errors have a uniform exponential majorant. -/
theorem coupled_iteration_le_dyadic_exp (c C T ε : ℝ) (hc : 0 ≤ c)
    (hC : 0 ≤ C) (hT : 0 < T) (hε : 0 < ε)
    (K P : ℕ → ℝ) (N : ℕ) (hK0 : 0 ≤ K 0) (hP : ∀ n, n < N → 0 ≤ P n)
    (hinit : P 0 ≤ 2 * c * K 0)
    (hK : ∀ n, n < N → K (n + 1) = K n + (C * ((2 : ℝ) ^ n * T) ^ (-ε)) * P n)
    (hstep : ∀ n, n < N → P (n + 1) ≤ max (P n) (c * K (n + 1) + P n / 2))
    (n : ℕ) (hn : n ≤ N) :
    K n ≤ K 0 * Real.exp (2 * c * (C * T ^ (-ε)) / (1 - (2 : ℝ) ^ (-ε))) ∧
    P n ≤ 2 * c *
      (K 0 * Real.exp (2 * c * (C * T ^ (-ε)) / (1 - (2 : ℝ) ^ (-ε)))) := by
  have hweight (i : ℕ) :
      C * ((2 : ℝ) ^ i * T) ^ (-ε) =
        (C * T ^ (-ε)) * ((2 : ℝ) ^ (-ε)) ^ i := by
    rw [Real.mul_rpow (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) i) hT.le,
      ← Real.rpow_pow_comm (by norm_num : (0 : ℝ) ≤ 2)]
    ring
  apply coupled_iteration_le_geometric_exp c (C * T ^ (-ε)) ((2 : ℝ) ^ (-ε)) hc
    (mul_nonneg hC (Real.rpow_nonneg hT.le _))
    (Real.rpow_nonneg (by norm_num) _)
    (Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_neg_of_pos hε))
    K P N hK0 hP hinit _ hstep n hn
  intro i hi
  rw [← hweight i]
  exact hK i hi

end EinsteinFull
