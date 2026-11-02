import EinsteinFull.Frozen.LatticeConvolutionPower
import EinsteinFull.Frozen.RegenerationLatticeMass
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Uniform aperiodicity for lattice renewal generating functions

Deterministic support for the analytic argument in `paper/main.tex`, lines 379–391.
The analytic bounds apply to arbitrary nonnegative probability masses. The final
consumers specialize them to the literal regeneration law under explicit mass
and moment hypotheses; those hypotheses are not asserted for that law here.
-/

namespace EinsteinFull.Work.W5

/-- Every power of a point in the closed unit disc has real part at most one. -/
theorem re_pow_le_one {z : ℂ} (hz : ‖z‖ ≤ 1) (n : ℕ) : (z ^ n).re ≤ 1 := by
  calc
    (z ^ n).re ≤ ‖z ^ n‖ := Complex.re_le_norm _
    _ = ‖z‖ ^ n := norm_pow _ _
    _ ≤ 1 := pow_le_one₀ (norm_nonneg _) hz

private theorem eq_one_of_re_eq_one {w : ℂ} (hw : ‖w‖ ≤ 1)
    (hre : w.re = 1) : w = 1 := by
  have hn : ‖w‖ = 1 := le_antisymm hw (hre ▸ Complex.re_le_norm w)
  have hi : w.im = 0 := Complex.abs_re_eq_norm.mp (by rw [hre, hn, abs_one])
  exact Complex.ext hre hi

/-- The elementary two-mass deficit is nonnegative on the closed unit disc. -/
theorem two_mass_deficit_nonneg {z : ℂ} (hz : ‖z‖ ≤ 1) :
    0 ≤ 2 - (z ^ 2 + z ^ 3).re := by
  have h2 := re_pow_le_one hz 2
  have h3 := re_pow_le_one hz 3
  rw [Complex.add_re]
  linarith

/-- The two-mass deficit vanishes on the closed unit disc exactly at one. -/
theorem two_mass_deficit_eq_zero_iff {z : ℂ} (hz : ‖z‖ ≤ 1) :
    2 - (z ^ 2 + z ^ 3).re = 0 ↔ z = 1 := by
  constructor
  · intro h
    have h2 := re_pow_le_one hz 2
    have h3 := re_pow_le_one hz 3
    rw [Complex.add_re] at h
    have h2' : z ^ 2 = 1 := eq_one_of_re_eq_one
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz) (by linarith)
    have h3' : z ^ 3 = 1 := eq_one_of_re_eq_one
      (by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hz) (by linarith)
    calc
      z = z ^ 2 * z := by rw [h2', one_mul]
      _ = z ^ 3 := by ring
      _ = 1 := h3'
  · rintro rfl
    norm_num

/-- Away from any fixed ball about one, the deficit has a positive uniform
lower bound. The bound is selected before the point of the closed unit disc. -/
theorem exists_two_mass_deficit_lower_bound (h : ℝ) (hh : 0 < h) :
    ∃ c : ℝ, 0 < c ∧ ∀ z : ℂ, ‖z‖ ≤ 1 → h ≤ ‖z - 1‖ →
      c ≤ 2 - (z ^ 2 + z ^ 3).re := by
  let S : Set ℂ := Metric.closedBall 0 1 ∩ {z | h ≤ ‖z - 1‖}
  have hS : IsCompact S := (isCompact_closedBall (0 : ℂ) 1).inter_right
    (isClosed_le continuous_const (continuous_id.sub continuous_const).norm)
  obtain ⟨c, hc, hbound⟩ := hS.exists_forall_le'
    (by fun_prop : ContinuousOn (fun z : ℂ => 2 - (z ^ 2 + z ^ 3).re) S) (a := 0)
    (by
      intro z hz
      have hnorm : ‖z‖ ≤ 1 := by simpa using hz.1
      have hne : z ≠ 1 := by
        intro heq
        simpa [heq, hh.not_ge] using hz.2
      exact lt_of_le_of_ne (two_mass_deficit_nonneg hnorm)
        (Ne.symm (mt (two_mass_deficit_eq_zero_iff hnorm).mp hne)))
  refine ⟨c, hc, fun z hz hd => hbound z ⟨?_, hd⟩⟩
  simpa using hz

/-- Absolute summability of the probability generating series, including the
boundary of the unit disc. -/
theorem summable_norm_generating_series (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable p) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    Summable (fun n : ℕ => ‖(p n : ℂ) * z ^ n‖) := by
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [norm_mul, Complex.norm_of_nonneg (hp n), norm_pow]
  exact mul_le_of_le_one_right (hp n) (pow_le_one₀ (norm_nonneg _) hz)

/-- Positivity of the coefficients makes the real generating-function deficit
at least the contribution of the masses at two and three. -/
theorem two_mass_le_re_generating_deficit (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable p) (ht : ∑' n, p n = 1) (ε : ℝ)
    (h2 : ε ≤ p 2) (h3 : ε ≤ p 3) {z : ℂ} (hz : ‖z‖ ≤ 1) :
    ε * (2 - (z ^ 2 + z ^ 3).re) ≤
      (1 - ∑' n : ℕ, (p n : ℂ) * z ^ n).re := by
  have hseries := (summable_norm_generating_series p hp hs hz).of_norm
  have hreal := Complex.hasSum_re hseries.hasSum
  have hterm (n : ℕ) : ((p n : ℂ) * z ^ n).re = p n * (z ^ n).re := by
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  have hd : HasSum (fun n => p n * (1 - (z ^ n).re))
      (1 - (∑' n : ℕ, (p n : ℂ) * z ^ n).re) := by
    convert (hs.hasSum.sub hreal) using 1
    · ext n
      rw [hterm]
      ring
    · rw [ht]
  have hn (n : ℕ) : 0 ≤ p n * (1 - (z ^ n).re) :=
    mul_nonneg (hp n) (sub_nonneg.mpr (re_pow_le_one hz n))
  have hfin := hd.summable.sum_le_tsum ({2, 3} : Finset ℕ) (fun n _ => hn n)
  rw [hd.tsum_eq] at hfin
  norm_num only [Finset.sum_insert, Finset.mem_singleton, Finset.sum_singleton,
    show (2 : ℕ) ≠ 3 by omega, not_false_eq_true] at hfin
  have he2 := mul_le_mul_of_nonneg_right h2 (sub_nonneg.mpr (re_pow_le_one hz 2))
  have he3 := mul_le_mul_of_nonneg_right h3 (sub_nonneg.mpr (re_pow_le_one hz 3))
  rw [Complex.sub_re, Complex.one_re, Complex.add_re]
  linarith

/-- Uniform separation of the probability generating function from one away
from one in the closed unit disc. The constant depends only on ε and h and is
chosen before the mass sequence. -/
theorem exists_uniform_generating_deficit_lower_bound (ε h : ℝ)
    (hε : 0 < ε) (hh : 0 < h) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ p : ℕ → ℝ, (∀ n, 0 ≤ p n) → Summable p →
      (∑' n, p n) = 1 → ε ≤ p 2 → ε ≤ p 3 →
      ∀ z : ℂ, ‖z‖ ≤ 1 → h ≤ ‖z - 1‖ →
        κ ≤ ‖1 - ∑' n : ℕ, (p n : ℂ) * z ^ n‖ := by
  obtain ⟨c, hc, hbound⟩ := exists_two_mass_deficit_lower_bound h hh
  refine ⟨ε * c, mul_pos hε hc, ?_⟩
  intro p hp hs ht h2 h3 z hz hd
  exact (mul_le_mul_of_nonneg_left (hbound z hz hd) hε.le).trans
    ((two_mass_le_re_generating_deficit p hp hs ht ε h2 h3 hz).trans
      (Complex.re_le_norm _))

/-- Literal convolution powers preserve nonnegative coefficients. -/
theorem latticeConvolutionPower_nonneg (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (j n : ℕ) : 0 ≤ latticeConvolutionPower p j n := by
  induction j generalizing n with
  | zero => simp only [latticeConvolutionPower]; split_ifs <;> norm_num
  | succ j ih =>
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hp k) (ih (n - k)))

private theorem weighted_latticeConvolutionPower_succ (p : ℕ → ℝ)
    (j n : ℕ) (z : ℂ) :
    (latticeConvolutionPower p (j + 1) n : ℂ) * z ^ n =
      ∑ k ∈ Finset.range (n + 1),
        ((p k : ℂ) * z ^ k) * ((latticeConvolutionPower p j (n - k) : ℂ) * z ^ (n - k)) := by
  rw [latticeConvolutionPower, Complex.ofReal_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
  have hz : z ^ n = z ^ k * z ^ (n - k) := by
    rw [← pow_add, Nat.add_sub_of_le hkn]
  rw [Complex.ofReal_mul, hz]
  ring

/-- The Cauchy product identity for every literal lattice convolution power,
with absolute summability on the entire closed unit disc. -/
theorem latticeConvolutionPower_generating_series (p : ℕ → ℝ)
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p) {z : ℂ} (hz : ‖z‖ ≤ 1) (j : ℕ) :
    Summable (fun n : ℕ => ‖(latticeConvolutionPower p j n : ℂ) * z ^ n‖) ∧
    HasSum (fun n : ℕ => (latticeConvolutionPower p j n : ℂ) * z ^ n)
      ((∑' n : ℕ, (p n : ℂ) * z ^ n) ^ j) := by
  induction j with
  | zero =>
    have heq : (fun n : ℕ => (latticeConvolutionPower p 0 n : ℂ) * z ^ n) =
        (fun n : ℕ => if n = 0 then 1 else 0) := by
      funext n
      simp only [latticeConvolutionPower]
      split_ifs with hn
      · subst n; simp only [Complex.ofReal_one, pow_zero, mul_one]
      · simp only [Complex.ofReal_zero, zero_mul]
    rw [heq]
    simp only [pow_zero]
    constructor
    · convert (hasSum_ite_eq 0 (1 : ℂ)).summable.norm using 1
      funext n
      simp only [latticeConvolutionPower]
      split_ifs with hn
      · subst n; simp only [Complex.ofReal_one, pow_zero, mul_one]
      · simp only [Complex.ofReal_zero, zero_mul]
    · exact hasSum_ite_eq 0 1
  | succ j ih =>
    have hpn := summable_norm_generating_series p hp hs hz
    have hnorm := summable_norm_sum_mul_range_of_summable_norm hpn ih.1
    have hsum := hasSum_sum_range_mul_of_summable_norm hpn ih.1
    simp_rw [← weighted_latticeConvolutionPower_succ] at hnorm hsum
    refine ⟨hnorm, ?_⟩
    rw [ih.2.tsum_eq, ← pow_succ'] at hsum
    exact hsum

/-- The uniform aperiodicity bound applies to the actual first convolution
power's generating series, rather than a substitute formal power series. -/
theorem exists_uniform_first_convolution_deficit_lower_bound (ε h : ℝ)
    (hε : 0 < ε) (hh : 0 < h) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ p : ℕ → ℝ, (∀ n, 0 ≤ p n) → Summable p →
      (∑' n, p n) = 1 → ε ≤ p 2 → ε ≤ p 3 →
      ∀ z : ℂ, ‖z‖ ≤ 1 → h ≤ ‖z - 1‖ →
        κ ≤ ‖1 - ∑' n : ℕ, (latticeConvolutionPower p 1 n : ℂ) * z ^ n‖ := by
  obtain ⟨κ, hκ, hb⟩ := exists_uniform_generating_deficit_lower_bound ε h hε hh
  refine ⟨κ, hκ, ?_⟩
  intro p hp hs ht h2 h3 z hz hd
  rw [(latticeConvolutionPower_generating_series p hp hs hz 1).2.tsum_eq, pow_one]
  exact hb p hp hs ht h2 h3 z hz hd

/-- A positive mass at two makes the generating series strictly contractive
inside the unit disc, even if there is a mass at zero. -/
theorem norm_generating_series_lt_one (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable p) (ht : ∑' n, p n = 1) (h2 : 0 < p 2)
    {z : ℂ} (hz : ‖z‖ < 1) : ‖∑' n : ℕ, (p n : ℂ) * z ^ n‖ < 1 := by
  have hnorm := summable_norm_generating_series p hp hs hz.le
  have hle (n : ℕ) : ‖(p n : ℂ) * z ^ n‖ ≤ p n := by
    rw [norm_mul, Complex.norm_of_nonneg (hp n), norm_pow]
    exact mul_le_of_le_one_right (hp n) (pow_le_one₀ (norm_nonneg _) hz.le)
  have hlt : ‖(p 2 : ℂ) * z ^ 2‖ < p 2 := by
    rw [norm_mul, Complex.norm_of_nonneg (hp 2), norm_pow]
    exact mul_lt_of_lt_one_right h2 (pow_lt_one₀ (norm_nonneg _) hz (by omega))
  exact (norm_tsum_le_tsum_norm hnorm).trans_lt
    (ht ▸ Summable.tsum_lt_tsum hle hlt hnorm hs)

/-- The sum of the generating functions of the literal convolution powers is
the renewal resolvent inside the unit disc. -/
theorem hasSum_latticeConvolutionPower_generating_series (p : ℕ → ℝ)
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p) (ht : ∑' n, p n = 1)
    (h2 : 0 < p 2) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun j : ℕ => ∑' n : ℕ, (latticeConvolutionPower p j n : ℂ) * z ^ n)
      (1 - ∑' n : ℕ, (p n : ℂ) * z ^ n)⁻¹ := by
  have heq (j : ℕ) := (latticeConvolutionPower_generating_series p hp hs hz.le j).2.tsum_eq
  simp_rw [heq]
  exact hasSum_geometric_of_norm_lt_one (norm_generating_series_lt_one p hp hs ht h2 hz)

private theorem latticeConvolutionPower_real_generating_series (p : ℕ → ℝ)
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p) {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (j : ℕ) : HasSum (fun n : ℕ => latticeConvolutionPower p j n * r ^ n)
      ((∑' n : ℕ, p n * r ^ n) ^ j) := by
  have hz : ‖(r : ℂ)‖ ≤ 1 := by rw [Complex.norm_of_nonneg hr]; exact hr1
  have H := (latticeConvolutionPower_generating_series p hp hs hz j).2
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_tsum] at H
  exact Complex.hasSum_ofReal.mp H

/-- Absolute summability of the entire literal renewal generating double
series inside the unit disc, justifying the exchange of cycle and time sums. -/
theorem summable_norm_latticeConvolutionPower_double_series (p : ℕ → ℝ)
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p) (ht : ∑' n, p n = 1)
    (h2 : 0 < p 2) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable (fun jn : ℕ × ℕ =>
      ‖(latticeConvolutionPower p jn.1 jn.2 : ℂ) * z ^ jn.2‖) := by
  have hn (j n : ℕ) : ‖(latticeConvolutionPower p j n : ℂ) * z ^ n‖ =
      latticeConvolutionPower p j n * ‖z‖ ^ n := by
    rw [norm_mul, Complex.norm_of_nonneg (latticeConvolutionPower_nonneg p hp j n), norm_pow]
  apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
  refine ⟨fun j => (latticeConvolutionPower_generating_series p hp hs hz.le j).1, ?_⟩
  simp_rw [hn, (latticeConvolutionPower_real_generating_series p hp hs (norm_nonneg z) hz.le _).tsum_eq]
  have hrad : ‖(‖z‖ : ℂ)‖ < 1 := by rw [Complex.norm_of_nonneg (norm_nonneg z)]; exact hz
  have H := norm_generating_series_lt_one p hp hs ht h2 hrad
  simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_tsum,
    Complex.norm_real] at H
  exact summable_geometric_of_abs_lt_one H

/-- The coefficients of the renewal resolvent are exactly the infinite sums
of the literal lattice convolution powers. This is the interior series bridge;
it asserts no continuation beyond the unit disc or rate of coefficient decay. -/
theorem hasSum_renewal_generating_series (p : ℕ → ℝ)
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p) (ht : ∑' n, p n = 1)
    (h2 : 0 < p 2) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (↑(∑' j : ℕ, latticeConvolutionPower p j n : ℝ) : ℂ) * z ^ n)
      (1 - ∑' n : ℕ, (p n : ℂ) * z ^ n)⁻¹ := by
  have hd := (summable_norm_latticeConvolutionPower_double_series p hp hs ht h2 hz).of_norm
  have hswap := hd.prod_symm
  rw [show (fun n : ℕ => (↑(∑' j : ℕ, latticeConvolutionPower p j n : ℝ) : ℂ) * z ^ n) =
      (fun n : ℕ => ∑' j : ℕ, (latticeConvolutionPower p j n : ℂ) * z ^ n) by
    funext n
    rw [Complex.ofReal_tsum, tsum_mul_right]]
  apply hswap.prod.hasSum_iff.mpr
  change (∑' n : ℕ, ∑' j : ℕ, (latticeConvolutionPower p j n : ℂ) * z ^ n) = _
  rw [Summable.tsum_comm (f := fun j n : ℕ =>
    (latticeConvolutionPower p j n : ℂ) * z ^ n) hd]
  exact (hasSum_latticeConvolutionPower_generating_series p hp hs ht h2 hz).tsum_eq

/-- Absolute summability throughout a disc from a summable radial majorant. -/
theorem summable_norm_generating_series_of_radius (p : ℕ → ℝ)
    (hp : ∀ n, 0 ≤ p n) {R : ℝ}
    (hs : Summable (fun n : ℕ => p n * R ^ n)) {z : ℂ} (hz : ‖z‖ ≤ R) :
    Summable (fun n : ℕ => ‖(p n : ℂ) * z ^ n‖) := by
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [norm_mul, Complex.norm_of_nonneg (hp n), norm_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz n) (hp n)

private theorem norm_pow_sub_pow_le (R : ℝ) (hR : 1 ≤ R)
    {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) (n : ℕ) :
    ‖z ^ n - w ^ n‖ ≤ (n : ℝ) * R ^ n * ‖z - w‖ := by
  have hR0 := zero_le_one.trans hR
  induction n with
  | zero => simp only [pow_zero, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    have heq : z ^ (n + 1) - w ^ (n + 1) =
        z ^ n * (z - w) + (z ^ n - w ^ n) * w := by ring
    have hpow : ‖z ^ n‖ ≤ R ^ n := by
      rw [norm_pow]
      exact pow_le_pow_left₀ (norm_nonneg _) hz n
    have hRD : R ^ n * ‖z - w‖ ≤ R ^ n * ‖z - w‖ * R :=
      le_mul_of_one_le_right (mul_nonneg (pow_nonneg hR0 _) (norm_nonneg _)) hR
    calc
      ‖z ^ (n + 1) - w ^ (n + 1)‖ ≤
          ‖z ^ n‖ * ‖z - w‖ + ‖z ^ n - w ^ n‖ * ‖w‖ := by
        rw [heq]
        exact (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ R ^ n * ‖z - w‖ + ((n : ℝ) * R ^ n * ‖z - w‖) * R :=
        add_le_add (mul_le_mul_of_nonneg_right hpow (norm_nonneg _))
          (mul_le_mul ih hw (norm_nonneg _) (by positivity))
      _ ≤ ((n + 1 : ℕ) : ℝ) * R ^ (n + 1) * ‖z - w‖ := by
        rw [Nat.cast_add, Nat.cast_one, pow_succ]
        nlinarith only [hRD]

/-- A radial first-moment bound gives a uniform Lipschitz bound for the literal
generating series on a larger disc. All moment hypotheses are on the masses. -/
theorem norm_generating_series_sub_le (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    {R K : ℝ} (hR : 1 ≤ R) (hs : Summable (fun n : ℕ => p n * R ^ n))
    (hm : Summable (fun n : ℕ => p n * (n : ℝ) * R ^ n))
    (hK : (∑' n : ℕ, p n * (n : ℝ) * R ^ n) ≤ K)
    {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖(∑' n : ℕ, (p n : ℂ) * z ^ n) - ∑' n : ℕ, (p n : ℂ) * w ^ n‖ ≤
      K * ‖z - w‖ := by
  have hzs := (summable_norm_generating_series_of_radius p hp hs hz).of_norm
  have hws := (summable_norm_generating_series_of_radius p hp hs hw).of_norm
  have hterm (n : ℕ) : ‖(p n : ℂ) * z ^ n - (p n : ℂ) * w ^ n‖ ≤
      (p n * (n : ℝ) * R ^ n) * ‖z - w‖ := by
    rw [← mul_sub, norm_mul, Complex.norm_of_nonneg (hp n)]
    calc
      p n * ‖z ^ n - w ^ n‖ ≤ p n * ((n : ℝ) * R ^ n * ‖z - w‖) :=
        mul_le_mul_of_nonneg_left (norm_pow_sub_pow_le R hR hz hw n) (hp n)
      _ = _ := by ring
  exact ((hzs.hasSum.sub hws.hasSum).norm_le_of_bounded
    (hm.hasSum.mul_right ‖z - w‖) hterm).trans
      (mul_le_mul_of_nonneg_right hK (norm_nonneg _))

private theorem exists_unit_radial_projection {z : ℂ} (hz : 1 < ‖z‖) :
    ∃ w : ℂ, ‖w‖ = 1 ∧ ‖z - w‖ = ‖z‖ - 1 := by
  let w := z / (‖z‖ : ℂ)
  have hnorm : 0 < ‖z‖ := lt_trans zero_lt_one hz
  have hn0 : (‖z‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hnorm.ne'
  have hw : ‖w‖ = 1 := by
    dsimp [w]
    rw [norm_div, Complex.norm_of_nonneg hnorm.le, div_self hnorm.ne']
  refine ⟨w, hw, ?_⟩
  have heq : z - w = ((‖z‖ - 1 : ℝ) : ℂ) * w := by
    dsimp [w]
    push_cast
    field_simp
  rw [heq, norm_mul, Complex.norm_of_nonneg (sub_nonneg.mpr hz.le), hw, mul_one]

/-- The compact aperiodicity bound extends to a uniform annulus away from one.
The radius is selected before the probability masses, using only the fixed
mass lower bound, exclusion radius, disc radius and radial moment bound. -/
theorem exists_uniform_annular_generating_deficit_lower_bound (ε h R K : ℝ)
    (hε : 0 < ε) (hh : 0 < h) (hR : 1 < R) (hK : 0 ≤ K) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧ 1 + ρ ≤ R ∧ ρ ≤ h ∧
      ∀ p : ℕ → ℝ, (∀ n, 0 ≤ p n) → Summable p → (∑' n, p n) = 1 →
        ε ≤ p 2 → ε ≤ p 3 →
        Summable (fun n : ℕ => p n * R ^ n) →
        Summable (fun n : ℕ => p n * (n : ℝ) * R ^ n) →
        (∑' n : ℕ, p n * (n : ℝ) * R ^ n) ≤ K →
        ∀ z : ℂ, ‖z‖ ≤ 1 + ρ → 2 * h ≤ ‖z - 1‖ →
          κ ≤ ‖1 - ∑' n : ℕ, (p n : ℂ) * z ^ n‖ := by
  obtain ⟨c, hc, hb⟩ := exists_uniform_generating_deficit_lower_bound ε h hε hh
  let ρ := min (R - 1) (min h (c / (2 * (K + 1))))
  have hρ : 0 < ρ := lt_min (sub_pos.mpr hR)
    (lt_min hh (div_pos hc (by positivity)))
  have hρR : 1 + ρ ≤ R := by
    have := min_le_left (R - 1) (min h (c / (2 * (K + 1))))
    dsimp [ρ]
    linarith
  have hρh : ρ ≤ h := (min_le_right _ _).trans (min_le_left _ _)
  have hρc : ρ ≤ c / (2 * (K + 1)) := (min_le_right _ _).trans (min_le_right _ _)
  have hsmall : K * ρ ≤ c / 2 := by
    have hprod := (le_div_iff₀ (by positivity : 0 < 2 * (K + 1))).mp hρc
    nlinarith only [hprod, hρ]
  refine ⟨ρ, c / 2, hρ, half_pos hc, hρR, hρh, ?_⟩
  intro p hp hs ht h2 h3 hsR hm hmK z hz hd
  by_cases hz1 : ‖z‖ ≤ 1
  · exact (half_le_self hc.le).trans (hb p hp hs ht h2 h3 z hz1 (by linarith))
  · obtain ⟨w, hw, hdist⟩ := exists_unit_radial_projection (lt_of_not_ge hz1)
    have hzw : ‖z - w‖ ≤ ρ := by linarith
    have haway : h ≤ ‖w - 1‖ := by
      have htri : ‖z - 1‖ ≤ ‖z - w‖ + ‖w - 1‖ := by
        simpa only [sub_add_sub_cancel] using norm_add_le (z - w) (w - 1)
      linarith
    have hwR : ‖w‖ ≤ R := hw ▸ hR.le
    have hdiff := norm_generating_series_sub_le p hp hR.le hsR hm hmK (hz.trans hρR) hwR
    have hdiff' : ‖(∑' n : ℕ, (p n : ℂ) * z ^ n) -
        ∑' n : ℕ, (p n : ℂ) * w ^ n‖ ≤ c / 2 :=
      hdiff.trans ((mul_le_mul_of_nonneg_left hzw hK).trans hsmall)
    have hbase := hb p hp hs ht h2 h3 w hw.le haway
    have htri : ‖1 - ∑' n : ℕ, (p n : ℂ) * w ^ n‖ ≤
        ‖1 - ∑' n : ℕ, (p n : ℂ) * z ^ n‖ +
        ‖(∑' n : ℕ, (p n : ℂ) * z ^ n) - ∑' n : ℕ, (p n : ℂ) * w ^ n‖ := by
      simpa only [sub_add_sub_cancel] using norm_add_le
        (1 - ∑' n : ℕ, (p n : ℂ) * z ^ n)
        ((∑' n : ℕ, (p n : ℂ) * z ^ n) - ∑' n : ℕ, (p n : ℂ) * w ^ n)
    linarith

/-- An exponential moment at a larger radius controls a radial first moment
at a smaller radius, with a bound chosen before the nonnegative sequence. -/
theorem exists_radial_first_moment_bound (R S M : ℝ) (hR : 1 ≤ R)
    (hRS : R < S) (hM : 0 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ p : ℕ → ℝ, (∀ n, 0 ≤ p n) →
      Summable (fun n : ℕ => p n * S ^ n) → (∑' n : ℕ, p n * S ^ n) ≤ M →
      Summable (fun n : ℕ => p n * R ^ n) ∧
      Summable (fun n : ℕ => p n * (n : ℝ) * R ^ n) ∧
      (∑' n : ℕ, p n * (n : ℝ) * R ^ n) ≤ K := by
  have hR0 := zero_le_one.trans hR
  have hS : 0 < S := (lt_of_lt_of_le zero_lt_one hR).trans hRS
  have hratio : ‖R / S‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hR0 hS.le)]
    exact (div_lt_one hS).mpr hRS
  have hgeom : Summable (fun n : ℕ => (n : ℝ) * (R / S) ^ n) := by
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hratio
  have hgeom0 (n : ℕ) : 0 ≤ (n : ℝ) * (R / S) ^ n := by positivity
  let C := 1 + ∑' n : ℕ, (n : ℝ) * (R / S) ^ n
  have hC : 0 < C := by
    have : 0 ≤ ∑' n : ℕ, (n : ℝ) * (R / S) ^ n := tsum_nonneg hgeom0
    dsimp [C]
    linarith
  have hcoef (n : ℕ) : (n : ℝ) * R ^ n ≤ C * S ^ n := by
    have hn := hgeom.sum_le_tsum ({n} : Finset ℕ) (fun i _ => hgeom0 i)
    simp only [Finset.sum_singleton] at hn
    have hCn : (n : ℝ) * (R / S) ^ n ≤ C := by dsimp [C]; linarith
    have heq : (R / S) ^ n * S ^ n = R ^ n := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hS.ne')]
    calc
      (n : ℝ) * R ^ n = ((n : ℝ) * (R / S) ^ n) * S ^ n := by rw [mul_assoc, heq]
      _ ≤ C * S ^ n := mul_le_mul_of_nonneg_right hCn (pow_nonneg hS.le _)
  refine ⟨C * M, mul_pos hC hM, ?_⟩
  intro p hp hs hm
  have hpoint (n : ℕ) : p n * (n : ℝ) * R ^ n ≤ C * (p n * S ^ n) := by
    have := mul_le_mul_of_nonneg_left (hcoef n) (hp n)
    nlinarith only [this]
  have hfirst := (hs.mul_left C).of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (hp n) (Nat.cast_nonneg _))
    (pow_nonneg hR0 _)) hpoint
  refine ⟨hs.of_nonneg_of_le (fun n => mul_nonneg (hp n) (pow_nonneg hR0 _))
    (fun n => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hR0 hRS.le n) (hp n)), hfirst, ?_⟩
  exact (hfirst.tsum_le_tsum hpoint (hs.mul_left C)).trans
    (by rw [tsum_mul_left]; exact mul_le_mul_of_nonneg_left hm hC.le)

/-- Annular separation from one under a single uniform exponential moment.
The two constants are chosen before p, and depend only on ε, h, a and M. -/
theorem exists_uniform_annular_deficit_of_exponential_moment (ε h a M : ℝ)
    (hε : 0 < ε) (hh : 0 < h) (ha : 0 < a) (hM : 0 < M) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧ 1 + ρ ≤ Real.exp (a / 2) ∧ ρ ≤ h ∧
      ∀ p : ℕ → ℝ, (∀ n, 0 ≤ p n) → (∑' n : ℕ, p n) = 1 →
        ε ≤ p 2 → ε ≤ p 3 →
        Summable (fun n : ℕ => p n * Real.exp (a * (n : ℝ))) →
        (∑' n : ℕ, p n * Real.exp (a * (n : ℝ))) ≤ M →
        ∀ z : ℂ, ‖z‖ ≤ 1 + ρ → 2 * h ≤ ‖z - 1‖ →
          κ ≤ ‖1 - ∑' n : ℕ, (p n : ℂ) * z ^ n‖ := by
  have hR : 1 < Real.exp (a / 2) := Real.one_lt_exp_iff.mpr (half_pos ha)
  have hRS : Real.exp (a / 2) < Real.exp a := Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨K, hK, hmom⟩ := exists_radial_first_moment_bound
    (Real.exp (a / 2)) (Real.exp a) M hR.le hRS hM
  obtain ⟨ρ, κ, hρ, hκ, hρR, hρh, hb⟩ :=
    exists_uniform_annular_generating_deficit_lower_bound ε h (Real.exp (a / 2)) K hε hh hR hK.le
  refine ⟨ρ, κ, hρ, hκ, hρR, hρh, ?_⟩
  intro p hp ht h2 h3 hs hm z hz hd
  have hs' : Summable (fun n : ℕ => p n * (Real.exp a) ^ n) := by
    simpa only [mul_comm a, Real.exp_nat_mul] using hs
  have hm' : (∑' n : ℕ, p n * (Real.exp a) ^ n) ≤ M := by
    simpa only [mul_comm a, Real.exp_nat_mul] using hm
  obtain ⟨hsR, hfirst, hfirstK⟩ := hmom p hp hs' hm'
  have hsp : Summable p := hs'.of_nonneg_of_le hp
    (fun n => le_mul_of_one_le_right (hp n)
      (one_le_pow₀ ((hR.trans hRS).le)))
  exact hb p hp hsp ht h2 h3 hsR hfirst hfirstK z hz hd

/-- Each literal renewal coefficient is a convergent real sum over cycles. -/
theorem summable_latticeConvolutionPower_cycles (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable p) (ht : ∑' n, p n = 1) (h2 : 0 < p 2) (n : ℕ) :
    Summable (fun j : ℕ => latticeConvolutionPower p j n) := by
  have hd := (summable_norm_latticeConvolutionPower_double_series p hp hs ht h2
    (z := (1 / 2 : ℂ)) (by norm_num)).of_norm
  have hrow : Summable (fun j : ℕ =>
      (latticeConvolutionPower p j n : ℂ) * (1 / 2 : ℂ) ^ n) := hd.prod_symm.prod_factor n
  exact Complex.summable_ofReal.mp
    ((summable_mul_right_iff (pow_ne_zero n (by norm_num : (1 / 2 : ℂ) ≠ 0))).mp hrow)

open EinsteinRelation

/-- Nonnegativity follows directly from the literal regeneration mass as a
real measure value, with no renewal or tail input. -/
theorem regenerationLatticeMass_nonneg {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0) (n : ℕ) :
    0 ≤ regenerationLatticeMass hd Q lam l K hK hD n :=
  MeasureTheory.measureReal_nonneg

/-- Conditional specialization of the literal renewal-series identity to the
actual regeneration masses. Probability normalization, summability and the
positive mass at two remain explicit hypotheses. -/
theorem regenerationLatticeMass_renewal_generating_series {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (lam l : ℝ)
    (K : Regeneration.CoupledQuenchedLaws d)
    (hK : Regeneration.HasProbabilityLaws Q.measure K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0)
    (hs : Summable (regenerationLatticeMass hd Q lam l K hK hD))
    (ht : (∑' n : ℕ, regenerationLatticeMass hd Q lam l K hK hD n) = 1)
    (h2 : 0 < regenerationLatticeMass hd Q lam l K hK hD 2)
    {z : ℂ} (hz : ‖z‖ < 1) :
    let p := regenerationLatticeMass hd Q lam l K hK hD
    HasSum (fun n : ℕ => (↑(∑' j : ℕ, latticeConvolutionPower p j n : ℝ) : ℂ) * z ^ n)
      (1 - ∑' n : ℕ, (p n : ℂ) * z ^ n)⁻¹ :=
  hasSum_renewal_generating_series _ (regenerationLatticeMass_nonneg hd Q lam l K hK hD)
    hs ht h2 hz

/-- Uniform annular aperiodicity for the literal regeneration masses,
conditional on the explicitly listed mass and exponential-moment facts.
The constants precede the environment, force, coupling and resulting mass law. -/
theorem exists_regenerationLatticeMass_annular_deficit_of_mass_hypotheses (ε h a M : ℝ)
    (hε : 0 < ε) (hh : 0 < h) (ha : 0 < a) (hM : 0 < M) :
    ∃ ρ κ : ℝ, 0 < ρ ∧ 0 < κ ∧ 1 + ρ ≤ Real.exp (a / 2) ∧ ρ ≤ h ∧
      ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
        (lam l : ℝ) (K : Regeneration.CoupledQuenchedLaws d)
        (hK : Regeneration.HasProbabilityLaws Q.measure K)
        (hD : Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam)) ≠ 0),
      let p := regenerationLatticeMass hd Q lam l K hK hD
      (∑' n : ℕ, p n) = 1 → ε ≤ p 2 → ε ≤ p 3 →
        Summable (fun n : ℕ => p n * Real.exp (a * (n : ℝ))) →
        (∑' n : ℕ, p n * Real.exp (a * (n : ℝ))) ≤ M →
        ∀ z : ℂ, ‖z‖ ≤ 1 + ρ → 2 * h ≤ ‖z - 1‖ →
          κ ≤ ‖1 - ∑' n : ℕ, (p n : ℂ) * z ^ n‖ := by
  obtain ⟨ρ, κ, hρ, hκ, hρR, hρh, hb⟩ :=
    exists_uniform_annular_deficit_of_exponential_moment ε h a M hε hh ha hM
  refine ⟨ρ, κ, hρ, hκ, hρR, hρh, ?_⟩
  intro d hd Λ₀ r₀ Q lam l K hK hD
  exact hb _ (regenerationLatticeMass_nonneg hd Q lam l K hK hD)

end EinsteinFull.Work.W5
