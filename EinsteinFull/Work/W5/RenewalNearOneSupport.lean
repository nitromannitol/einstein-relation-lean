import EinsteinFull.Work.W5.RenewalAperiodicitySupport
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Analytic.IsolatedZeros

/-!
# The analytic renewal divided difference near one

Ordinary deterministic support for `paper/main.tex`, lines 379–391. All mass and
moment hypotheses below concern a generic sequence, not the regeneration law.
The extension is the convergent sum of the literal finite geometric polynomials.
-/

open Metric

noncomputable section

namespace EinsteinFull.Work.W5

/-- Literal probability generating series, retaining indices zero and one. -/
def renewalGenerating (p : ℕ → ℝ) (z : ℂ) : ℂ := ∑' n : ℕ, (p n : ℂ) * z ^ n

/-- The first moment of the literal mass sequence. -/
def renewalMean (p : ℕ → ℝ) : ℝ := ∑' n : ℕ, p n * (n : ℝ)

/-- Analytic candidate for `(1-p(z))/(1-z)`, including its value at one. -/
def renewalDividedDifference (p : ℕ → ℝ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, (p n : ℂ) * ∑ k ∈ Finset.range n, z ^ k

/-- A single radial exponential moment controls every polynomial moment at a
strictly smaller radius. The bound is chosen before the sequence. -/
theorem exists_radial_power_moment_bound (k : ℕ) (R S M : ℝ) (hR : 0 ≤ R)
    (hRS : R < S) (hM : 0 < M) :
    ∃ K : ℝ, 0 < K ∧ ∀ p : ℕ → ℝ, (∀ n, 0 ≤ p n) →
      Summable (fun n : ℕ => p n * S ^ n) → (∑' n : ℕ, p n * S ^ n) ≤ M →
      Summable (fun n : ℕ => p n * (n : ℝ) ^ k * R ^ n) ∧
      (∑' n : ℕ, p n * (n : ℝ) ^ k * R ^ n) ≤ K := by
  have hS : 0 < S := hR.trans_lt hRS
  have hratio : ‖R / S‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg hR hS.le)]
    exact (div_lt_one hS).mpr hRS
  have hg := summable_pow_mul_geometric_of_norm_lt_one k hratio
  have hg0 (n : ℕ) : 0 ≤ (n : ℝ) ^ k * (R / S) ^ n := by positivity
  let C := 1 + ∑' n : ℕ, (n : ℝ) ^ k * (R / S) ^ n
  have hC : 0 < C := by
    have : 0 ≤ ∑' n : ℕ, (n : ℝ) ^ k * (R / S) ^ n := tsum_nonneg hg0
    dsimp [C]
    linarith
  have hcoef (n : ℕ) : (n : ℝ) ^ k * R ^ n ≤ C * S ^ n := by
    have hn := hg.sum_le_tsum ({n} : Finset ℕ) (fun i _ => hg0 i)
    simp only [Finset.sum_singleton] at hn
    have hCn : (n : ℝ) ^ k * (R / S) ^ n ≤ C := by dsimp [C]; linarith
    have heq : (R / S) ^ n * S ^ n = R ^ n := by
      rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero _ hS.ne')]
    calc
      (n : ℝ) ^ k * R ^ n = ((n : ℝ) ^ k * (R / S) ^ n) * S ^ n := by
        rw [mul_assoc, heq]
      _ ≤ C * S ^ n := mul_le_mul_of_nonneg_right hCn (pow_nonneg hS.le _)
  refine ⟨C * M, mul_pos hC hM, ?_⟩
  intro p hp hs hm
  have hb (n : ℕ) : p n * (n : ℝ) ^ k * R ^ n ≤ C * (p n * S ^ n) := by
    simpa only [mul_assoc, mul_left_comm C] using
      mul_le_mul_of_nonneg_left (hcoef n) (hp n)
  have hsum := (hs.mul_left C).of_nonneg_of_le (fun n => mul_nonneg (mul_nonneg (hp n) (pow_nonneg (Nat.cast_nonneg n) k)) (pow_nonneg hR n)) hb
  refine ⟨hsum, (hsum.tsum_le_tsum hb (hs.mul_left C)).trans ?_⟩
  rw [tsum_mul_left]
  exact mul_le_mul_of_nonneg_left hm hC.le

private theorem norm_geometric_polynomial_le {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, z ^ k‖ ≤ (n : ℝ) * R ^ n := by
  calc
    ‖∑ k ∈ Finset.range n, z ^ k‖ ≤ ∑ k ∈ Finset.range n, ‖z ^ k‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, R ^ n := by
      apply Finset.sum_le_sum
      intro k hk
      rw [norm_pow]
      exact (pow_le_pow_left₀ (norm_nonneg _) hz k).trans
        (pow_le_pow_right₀ hR (Nat.le_of_lt (Finset.mem_range.mp hk)))
    _ = _ := by simp

private theorem norm_power_sub_one_le {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ (n : ℝ) * R ^ n * ‖z - 1‖ := by
  rw [← geom_sum_mul z n, norm_mul]
  exact mul_le_mul_of_nonneg_right (norm_geometric_polynomial_le hR hz n) (norm_nonneg _)

private theorem norm_geometric_polynomial_sub_le {R : ℝ} (hR : 1 ≤ R)
    {z : ℂ} (hz : ‖z‖ ≤ R) (n : ℕ) :
    ‖(∑ k ∈ Finset.range n, z ^ k) - (n : ℂ)‖ ≤
      (n : ℝ) ^ 2 * R ^ n * ‖z - 1‖ := by
  have heq : (∑ k ∈ Finset.range n, z ^ k) - (n : ℂ) =
      ∑ k ∈ Finset.range n, (z ^ k - 1) := by simp [Finset.sum_sub_distrib]
  rw [heq]
  calc
    ‖∑ k ∈ Finset.range n, (z ^ k - 1)‖ ≤
        ∑ k ∈ Finset.range n, ‖z ^ k - 1‖ := norm_sum_le _ _
    _ ≤ ∑ _k ∈ Finset.range n, (n : ℝ) * R ^ n * ‖z - 1‖ := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := Nat.le_of_lt (Finset.mem_range.mp hk)
      exact (norm_power_sub_one_le hR hz k).trans
        (mul_le_mul_of_nonneg_right (mul_le_mul (by exact_mod_cast hkn)
          (pow_le_pow_right₀ hR hkn) (by positivity) (by positivity)) (norm_nonneg _))
    _ = _ := by simp; ring

/-- Absolute convergence of the analytic candidate from a radial first moment. -/
theorem summable_norm_renewalDividedDifference (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    {R : ℝ} (hR : 1 ≤ R) (hs : Summable (fun n : ℕ => p n * (n : ℝ) * R ^ n))
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    Summable (fun n : ℕ => ‖(p n : ℂ) * ∑ k ∈ Finset.range n, z ^ k‖) := by
  apply hs.of_nonneg_of_le (fun _ => norm_nonneg _)
  intro n
  rw [norm_mul, Complex.norm_of_nonneg (hp n), mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_geometric_polynomial_le hR hz n) (hp n)

/-- The constructed extension is holomorphic, proved by a summable uniform
majorant for its finite polynomial terms. No analyticity is assumed. -/
theorem analyticOnNhd_renewalDividedDifference (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    {R : ℝ} (hR : 1 ≤ R) (hs : Summable (fun n : ℕ => p n * (n : ℝ) * R ^ n)) :
    AnalyticOnNhd ℂ (renewalDividedDifference p) (Metric.ball 0 R) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  apply Complex.differentiableOn_tsum_of_summable_norm hs
  · intro n
    exact (differentiable_const _ |>.mul
      (Differentiable.fun_sum fun k _ => differentiable_id.pow k)).differentiableOn
  · exact isOpen_ball
  · intro n z hz
    rw [norm_mul, Complex.norm_of_nonneg (hp n), mul_assoc]
    apply mul_le_mul_of_nonneg_left (norm_geometric_polynomial_le hR ?_ n) (hp n)
    exact (by simpa only [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < R).le

/-- Its value at one is exactly the first moment, including masses at zero/one. -/
theorem renewalDividedDifference_one (p : ℕ → ℝ) :
    renewalDividedDifference p 1 = (renewalMean p : ℂ) := by
  simp only [renewalDividedDifference, one_pow, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul, mul_one, renewalMean, Complex.ofReal_tsum, Complex.ofReal_mul,
    Complex.ofReal_natCast]

/-- Exact factorization of the literal generating deficit, on the closed disc. -/
theorem renewal_deficit_factorization (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable p) (ht : ∑' n, p n = 1) {R : ℝ} (hR : 1 ≤ R)
    (hsR : Summable (fun n : ℕ => p n * R ^ n))
    (hmR : Summable (fun n : ℕ => p n * (n : ℝ) * R ^ n))
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    1 - renewalGenerating p z = (1 - z) * renewalDividedDifference p z := by
  have hgen := (summable_norm_generating_series_of_radius p hp hsR hz).of_norm
  have hdiv := (summable_norm_renewalDividedDifference p hp hR hmR hz).of_norm
  have hmass : HasSum (fun n : ℕ => (p n : ℂ)) 1 := by
    simpa only [ht, Complex.ofReal_one] using (Complex.hasSum_ofReal.mpr hs.hasSum)
  have h := (hmass.sub hgen.hasSum).tsum_eq
  calc
    1 - renewalGenerating p z = ∑' n : ℕ, ((p n : ℂ) - (p n : ℂ) * z ^ n) := h.symm
    _ = ∑' n : ℕ, (1 - z) * ((p n : ℂ) * ∑ k ∈ Finset.range n, z ^ k) := by
      apply tsum_congr
      intro n
      have hg := geom_sum_mul z n
      calc
        (p n : ℂ) - (p n : ℂ) * z ^ n = (p n : ℂ) * (1 - z ^ n) := by ring
        _ = _ := by linear_combination (p n : ℂ) * hg
    _ = (1 - z) * renewalDividedDifference p z := (hdiv.hasSum.mul_left (1 - z)).tsum_eq

/-- Away from one this analytic candidate equals the requested quotient. -/
theorem renewalDividedDifference_eq_div (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable p) (ht : ∑' n, p n = 1) {R : ℝ} (hR : 1 ≤ R)
    (hsR : Summable (fun n : ℕ => p n * R ^ n))
    (hmR : Summable (fun n : ℕ => p n * (n : ℝ) * R ^ n))
    {z : ℂ} (hz : ‖z‖ ≤ R) (hz1 : z ≠ 1) :
    renewalDividedDifference p z = (1 - renewalGenerating p z) / (1 - z) := by
  rw [renewal_deficit_factorization p hp hs ht hR hsR hmR hz]
  exact (mul_div_cancel_left₀ _ (sub_ne_zero.mpr (Ne.symm hz1))).symm

/-- The actual divided difference has a quantitative remainder controlled by
one radial second moment. This is a finite-polynomial estimate followed by an
absolutely convergent sum, with no derivative interchange premise. -/
theorem norm_renewalDividedDifference_sub_mean_le (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    {R C : ℝ} (hR : 1 ≤ R)
    (hfirst : Summable (fun n : ℕ => p n * (n : ℝ) * R ^ n))
    (hsecond : Summable (fun n : ℕ => p n * (n : ℝ) ^ 2 * R ^ n))
    (hC : (∑' n : ℕ, p n * (n : ℝ) ^ 2 * R ^ n) ≤ C)
    {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖renewalDividedDifference p z - (renewalMean p : ℂ)‖ ≤ C * ‖z - 1‖ := by
  have hzs := (summable_norm_renewalDividedDifference p hp hR hfirst hz).of_norm
  have hones := (summable_norm_renewalDividedDifference p hp hR hfirst
    (z := 1) (by simpa using hR)).of_norm
  rw [← renewalDividedDifference_one]
  have hb (n : ℕ) :
      ‖(p n : ℂ) * (∑ k ∈ Finset.range n, z ^ k) -
        (p n : ℂ) * (∑ k ∈ Finset.range n, (1 : ℂ) ^ k)‖ ≤
      (p n * (n : ℝ) ^ 2 * R ^ n) * ‖z - 1‖ := by
    simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    rw [← mul_sub, norm_mul, Complex.norm_of_nonneg (hp n)]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
      (norm_geometric_polynomial_sub_le hR hz n) (hp n)
  exact ((hzs.hasSum.sub hones.hasSum).norm_le_of_bounded
    (hsecond.hasSum.mul_right ‖z - 1‖) hb).trans
      (mul_le_mul_of_nonneg_right hC (norm_nonneg _))

/-- The generating series itself is analytic inside every disc with a summable
radial majorant. -/
theorem analyticOnNhd_renewalGenerating (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    {R : ℝ} (hs : Summable (fun n : ℕ => p n * R ^ n)) :
    AnalyticOnNhd ℂ (renewalGenerating p) (Metric.ball 0 R) := by
  apply DifferentiableOn.analyticOnNhd _ isOpen_ball
  apply Complex.differentiableOn_tsum_of_summable_norm hs
  · intro n
    exact ((differentiable_const _).mul (differentiable_id.pow n)).differentiableOn
  · exact isOpen_ball
  · intro n z hz
    rw [norm_mul, Complex.norm_of_nonneg (hp n), norm_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _)
      (by simpa only [Metric.mem_ball, dist_zero_right] using hz : ‖z‖ < R).le n) (hp n)

/-- Summability and both radial moments follow from the single stated
exponential moment. Both numerical bounds precede the mass sequence. -/
theorem exists_renewal_moment_bounds (a M : ℝ) (ha : 0 < a) (hM : 0 < M) :
    ∃ K C : ℝ, 0 < K ∧ 0 < C ∧ ∀ p : ℕ → ℝ, (∀ n, 0 ≤ p n) →
      Summable (fun n : ℕ => p n * Real.exp (a * (n : ℝ))) →
      (∑' n : ℕ, p n * Real.exp (a * (n : ℝ))) ≤ M →
      Summable p ∧ Summable (fun n : ℕ => p n * Real.exp (a / 2) ^ n) ∧
      Summable (fun n : ℕ => p n * (n : ℝ) * Real.exp (a / 2) ^ n) ∧
      (∑' n : ℕ, p n * (n : ℝ) * Real.exp (a / 2) ^ n) ≤ K ∧
      Summable (fun n : ℕ => p n * (n : ℝ) ^ 2 * Real.exp (a / 2) ^ n) ∧
      (∑' n : ℕ, p n * (n : ℝ) ^ 2 * Real.exp (a / 2) ^ n) ≤ C := by
  have hR : 1 < Real.exp (a / 2) := Real.one_lt_exp_iff.mpr (half_pos ha)
  have hRS : Real.exp (a / 2) < Real.exp a := Real.exp_lt_exp.mpr (by linarith)
  obtain ⟨K, hK, hfirst⟩ := exists_radial_first_moment_bound
    (Real.exp (a / 2)) (Real.exp a) M hR.le hRS hM
  obtain ⟨C, hC, hsecond⟩ := exists_radial_power_moment_bound 2
    (Real.exp (a / 2)) (Real.exp a) M (Real.exp_pos _).le hRS hM
  refine ⟨K, C, hK, hC, ?_⟩
  intro p hp hs hm
  have hs' : Summable (fun n : ℕ => p n * (Real.exp a) ^ n) := by
    simpa only [mul_comm a, Real.exp_nat_mul] using hs
  have hm' : (∑' n : ℕ, p n * (Real.exp a) ^ n) ≤ M := by
    simpa only [mul_comm a, Real.exp_nat_mul] using hm
  obtain ⟨hsR, hf, hfK⟩ := hfirst p hp hs' hm'
  obtain ⟨hss, hssC⟩ := hsecond p hp hs' hm'
  have hsp := hsR.of_nonneg_of_le hp (fun n => le_mul_of_one_le_right (hp n)
    (one_le_pow₀ hR.le))
  exact ⟨hsp, hsR, hf, hfK, hss, hssC⟩

/-- A radial first moment gives the actual finite mean. -/
theorem summable_renewalMean (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    {R : ℝ} (hR : 1 ≤ R) (hs : Summable (fun n : ℕ => p n * (n : ℝ) * R ^ n)) :
    Summable (fun n : ℕ => p n * (n : ℝ)) := by
  exact hs.of_nonneg_of_le (fun n => mul_nonneg (hp n) (Nat.cast_nonneg _))
    (fun n => le_mul_of_one_le_right (mul_nonneg (hp n) (Nat.cast_nonneg _)) (one_le_pow₀ hR))

/-- The two distinguished masses alone imply `mean ≥ 5ε`. No support
restriction at indices zero or one is used. -/
theorem five_mul_le_renewalMean (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable (fun n : ℕ => p n * (n : ℝ))) (ε : ℝ)
    (h2 : ε ≤ p 2) (h3 : ε ≤ p 3) : 5 * ε ≤ renewalMean p := by
  have hf := hs.sum_le_tsum ({2, 3} : Finset ℕ) (fun n _ => mul_nonneg (hp n) (Nat.cast_nonneg _))
  norm_num only [Finset.sum_insert, Finset.mem_singleton, Finset.sum_singleton,
    show (2 : ℕ) ≠ 3 by omega, not_false_eq_true, Nat.cast_ofNat] at hf
  dsimp [renewalMean]
  linarith

/-- A derivative identity for the literal series, derived using its proved
factorization and analytic divided difference. -/
theorem hasDerivAt_renewalGenerating_one (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable p) (ht : ∑' n, p n = 1) {R : ℝ} (hR : 1 < R)
    (hsR : Summable (fun n : ℕ => p n * R ^ n))
    (hmR : Summable (fun n : ℕ => p n * (n : ℝ) * R ^ n)) :
    HasDerivAt (renewalGenerating p) (renewalMean p : ℂ) 1 := by
  have hmem : (1 : ℂ) ∈ Metric.ball 0 R := by simpa using hR
  have hg := (analyticOnNhd_renewalDividedDifference p hp hR.le hmR 1 hmem).differentiableAt.hasDerivAt
  have hd := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub
    (((hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub (hasDerivAt_id (1 : ℂ))).mul hg)
  have hd' : HasDerivAt (fun z : ℂ => 1 - (1 - z) * renewalDividedDifference p z)
      (renewalMean p : ℂ) 1 := by
    refine (show HasDerivAt
      (fun z : ℂ => 1 - (1 - z) * renewalDividedDifference p z) _ 1 from hd).congr_deriv ?_
    simp [renewalDividedDifference_one]
  apply hd'.congr_of_eventuallyEq
  filter_upwards [isOpen_ball.mem_nhds hmem] with z hz
  have hzR : ‖z‖ ≤ R := (by simpa using hz : ‖z‖ < R).le
  have hf := renewal_deficit_factorization p hp hs ht hR.le hsR hmR hzR
  linear_combination -hf

/-- Uniform analytic extension and near-one lower bound from one exponential
moment and the two masses. Constants precede both the law and the point. -/
theorem exists_uniform_renewal_near_one (ε a M : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hM : 0 < M) :
    ∃ C h : ℝ, 0 < C ∧ 0 < h ∧ 1 + 2 * h < Real.exp (a / 2) ∧
      ∀ p : ℕ → ℝ, (∀ n, 0 ≤ p n) → (∑' n, p n) = 1 →
        ε ≤ p 2 → ε ≤ p 3 →
        Summable (fun n : ℕ => p n * Real.exp (a * (n : ℝ))) →
        (∑' n : ℕ, p n * Real.exp (a * (n : ℝ))) ≤ M →
        AnalyticOnNhd ℂ (renewalDividedDifference p) (Metric.ball 0 (Real.exp (a / 2))) ∧
        renewalDividedDifference p 1 = (renewalMean p : ℂ) ∧
        5 * ε ≤ renewalMean p ∧
        (∀ z : ℂ, ‖z‖ ≤ Real.exp (a / 2) →
          ‖renewalDividedDifference p z - (renewalMean p : ℂ)‖ ≤ C * ‖z - 1‖) ∧
        (∀ z : ℂ, ‖z - 1‖ ≤ 2 * h → 5 * ε / 2 ≤ ‖renewalDividedDifference p z‖) := by
  have hR : 1 < Real.exp (a / 2) := Real.one_lt_exp_iff.mpr (half_pos ha)
  obtain ⟨K, C, _, hC, hmoment⟩ := exists_renewal_moment_bounds a M ha hM
  let h := min ((Real.exp (a / 2) - 1) / 4) (5 * ε / (4 * C))
  have hh : 0 < h := lt_min (div_pos (sub_pos.mpr hR) (by norm_num)) (by positivity)
  have hhR : 1 + 2 * h < Real.exp (a / 2) := by
    have := min_le_left ((Real.exp (a / 2) - 1) / 4) (5 * ε / (4 * C))
    dsimp [h]
    linarith
  have hhC : C * (2 * h) ≤ 5 * ε / 2 := by
    have hb := min_le_right ((Real.exp (a / 2) - 1) / 4) (5 * ε / (4 * C))
    have hb' := (le_div_iff₀ (by positivity : 0 < 4 * C)).mp hb
    dsimp [h]
    nlinarith only [hb']
  refine ⟨C, h, hC, hh, hhR, ?_⟩
  intro p hp _ht h2 h3 hs hm
  obtain ⟨_, _, hf, _, hss, hssC⟩ := hmoment p hp hs hm
  have hmean := five_mul_le_renewalMean p hp (summable_renewalMean p hp hR.le hf) ε h2 h3
  have hrem (z : ℂ) (hz : ‖z‖ ≤ Real.exp (a / 2)) :=
    norm_renewalDividedDifference_sub_mean_le p hp hR.le hf hss hssC hz
  refine ⟨analyticOnNhd_renewalDividedDifference p hp hR.le hf,
    renewalDividedDifference_one p, hmean, fun z hz => hrem z hz, ?_⟩
  intro z hz
  have hzR : ‖z‖ ≤ Real.exp (a / 2) := by
    have ht : ‖z‖ ≤ ‖z - 1‖ + 1 := by simpa using norm_add_le (z - 1) (1 : ℂ)
    linarith
  have hb := (hrem z hzR).trans ((mul_le_mul_of_nonneg_left hz hC.le).trans hhC)
  have htri : ‖(renewalMean p : ℂ)‖ ≤
      ‖renewalDividedDifference p z - (renewalMean p : ℂ)‖ + ‖renewalDividedDifference p z‖ := by
    simpa only [sub_add_cancel, norm_sub_rev] using
      norm_add_le ((renewalMean p : ℂ) - renewalDividedDifference p z) (renewalDividedDifference p z)
  rw [Complex.norm_of_nonneg (by linarith : 0 ≤ renewalMean p)] at htri
  linarith

/-- Uniform uniqueness and simplicity of the zero at one on a larger closed
complex disc. Analyticity, the derivative, and absence of other zeros are all
conclusions from the probability, two-mass and single-moment hypotheses. -/
theorem exists_uniform_renewal_simple_zero (ε a M : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hM : 0 < M) :
    ∃ ρ : ℝ, 0 < ρ ∧ 1 + ρ < Real.exp (a / 2) ∧
      ∀ p : ℕ → ℝ, (∀ n, 0 ≤ p n) → (∑' n, p n) = 1 →
        ε ≤ p 2 → ε ≤ p 3 →
        Summable (fun n : ℕ => p n * Real.exp (a * (n : ℝ))) →
        (∑' n : ℕ, p n * Real.exp (a * (n : ℝ))) ≤ M →
        AnalyticOnNhd ℂ (renewalGenerating p) (Metric.ball 0 (Real.exp (a / 2))) ∧
        5 * ε ≤ renewalMean p ∧
        HasDerivAt (renewalGenerating p) (renewalMean p : ℂ) 1 ∧
        deriv (fun z : ℂ => 1 - renewalGenerating p z) 1 ≠ 0 ∧
        (∀ z : ℂ, ‖z‖ ≤ 1 + ρ →
          (1 - renewalGenerating p z = 0 ↔ z = 1)) := by
  have hR : 1 < Real.exp (a / 2) := Real.one_lt_exp_iff.mpr (half_pos ha)
  obtain ⟨C, h, _hC, hh, hhR, hnear⟩ := exists_uniform_renewal_near_one ε a M hε ha hM
  obtain ⟨ρ, κ, hρ, hκ, _hρR, hρh, hann⟩ :=
    exists_uniform_annular_deficit_of_exponential_moment ε h a M hε hh ha hM
  obtain ⟨K, D, _, _, hmoment⟩ := exists_renewal_moment_bounds a M ha hM
  have hρR : 1 + ρ < Real.exp (a / 2) := by linarith
  refine ⟨ρ, hρ, hρR, ?_⟩
  intro p hp ht h2 h3 hs hm
  obtain ⟨hsp, hsR, hf, _, _, _⟩ := hmoment p hp hs hm
  obtain ⟨_hg, _hg1, hmean, _hrem, hlower⟩ := hnear p hp ht h2 h3 hs hm
  have hd := hasDerivAt_renewalGenerating_one p hp hsp ht hR hsR hf
  have hddef := (hasDerivAt_const (1 : ℂ) (1 : ℂ)).sub hd
  have hmpos : 0 < renewalMean p := lt_of_lt_of_le (by positivity : 0 < 5 * ε) hmean
  refine ⟨analyticOnNhd_renewalGenerating p hp hsR, hmean, hd, ?_, ?_⟩
  · change deriv ((fun _ : ℂ => (1 : ℂ)) - renewalGenerating p) 1 ≠ 0
    rw [hddef.deriv]
    simpa using (Complex.ofReal_ne_zero.mpr hmpos.ne')
  · intro z hz
    constructor
    · intro hz0
      by_cases hzn : ‖z - 1‖ ≤ 2 * h
      · have hg0 := renewal_deficit_factorization p hp hsp ht hR.le hsR hf (hz.trans hρR.le)
        rw [hz0] at hg0
        have hgn : renewalDividedDifference p z ≠ 0 := by
          intro heq
          have := hlower z hzn
          rw [heq, norm_zero] at this
          linarith
        exact (sub_eq_zero.mp ((mul_eq_zero.mp hg0.symm).resolve_right hgn)).symm
      · have hb := hann p hp ht h2 h3 hs hm z hz (le_of_lt (lt_of_not_ge hzn))
        change κ ≤ ‖1 - renewalGenerating p z‖ at hb
        rw [hz0, norm_zero] at hb
        exact False.elim (hκ.not_ge hb)
    · rintro rfl
      have hf1 := renewal_deficit_factorization p hp hsp ht hR.le hsR hf
        (z := 1) (by simpa using hR.le)
      simpa only [sub_self, zero_mul] using hf1

/-- The removable renewal difference. Its value at one uses the derivative of
our constructed analytic extension, rather than division by zero. -/
def renewalRemovableDifference (p : ℕ → ℝ) (z : ℂ) : ℂ :=
  dslope (renewalDividedDifference p) 1 z /
    ((renewalMean p : ℂ) * renewalDividedDifference p z)

private theorem analyticAt_renewal_dslope {p : ℕ → ℝ} {z : ℂ}
    (hz : AnalyticAt ℂ (renewalDividedDifference p) z)
    (h1 : AnalyticAt ℂ (renewalDividedDifference p) 1) :
    AnalyticAt ℂ (dslope (renewalDividedDifference p) 1) z := by
  by_cases heq : z = 1
  · subst z
    obtain ⟨s, hs⟩ := h1
    exact ⟨s.fslope, hs.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℂ (fun w : ℂ =>
        (renewalDividedDifference p w - renewalDividedDifference p 1) / (w - 1)) z :=
      (hz.sub analyticAt_const).fun_div
        (analyticAt_id.sub analyticAt_const) (sub_ne_zero.mpr heq)
    have hsl : AnalyticAt ℂ (slope (renewalDividedDifference p) 1) z := by
      have he : slope (renewalDividedDifference p) 1 = (fun w : ℂ =>
          (renewalDividedDifference p w - renewalDividedDifference p 1) / (w - 1)) := by
        funext w
        exact slope_def_field _ _ _
      rw [he]
      exact hq
    exact hsl.congr (dslope_eventuallyEq_slope_of_ne _ heq).symm

/-- The extension agrees with the literal difference of inverses at every
nonunit point where the two denominators are nonzero. -/
theorem renewalRemovableDifference_eq (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable p) (ht : ∑' n, p n = 1) {R : ℝ} (hR : 1 ≤ R)
    (hsR : Summable (fun n : ℕ => p n * R ^ n))
    (hmR : Summable (fun n : ℕ => p n * (n : ℝ) * R ^ n))
    {z : ℂ} (hz : ‖z‖ ≤ R) (hz1 : z ≠ 1) (hm : renewalMean p ≠ 0)
    (hg : renewalDividedDifference p z ≠ 0) :
    renewalRemovableDifference p z = (1 - renewalGenerating p z)⁻¹ -
      ((renewalMean p : ℂ) * (1 - z))⁻¹ := by
  rw [renewalRemovableDifference, dslope_of_ne _ hz1, slope_def_field,
    renewalDividedDifference_one, renewal_deficit_factorization p hp hs ht hR hsR hmR hz]
  have hm' := Complex.ofReal_ne_zero.mpr hm
  have hz' := sub_ne_zero.mpr hz1
  have hz'' := sub_ne_zero.mpr (Ne.symm hz1)
  field_simp
  ring

/-- The removed value is the genuine derivative divided by the mean squared. -/
theorem renewalRemovableDifference_one (p : ℕ → ℝ) :
    renewalRemovableDifference p 1 = deriv (renewalDividedDifference p) 1 /
      (renewalMean p : ℂ) ^ 2 := by
  simp only [renewalRemovableDifference, dslope_same, renewalDividedDifference_one, pow_two]

private theorem norm_renewal_dslope_le {p : ℕ → ℝ} {R C : ℝ}
    (hR : 1 < R) (hC : 0 ≤ C)
    (hb : ∀ z : ℂ, ‖z‖ ≤ R →
      ‖renewalDividedDifference p z - (renewalMean p : ℂ)‖ ≤ C * ‖z - 1‖)
    {z : ℂ} (hz : ‖z‖ ≤ R) : ‖dslope (renewalDividedDifference p) 1 z‖ ≤ C := by
  by_cases heq : z = 1
  · subst z
    rw [dslope_same]
    apply norm_deriv_le_of_lip' hC
    have hmem : (1 : ℂ) ∈ Metric.ball 0 R := by simpa using hR
    filter_upwards [isOpen_ball.mem_nhds hmem] with w hw
    rw [renewalDividedDifference_one]
    exact hb w (by simpa using (le_of_lt (Metric.mem_ball.mp hw)))
  · rw [dslope_of_ne _ heq, slope_def_field, renewalDividedDifference_one, norm_div]
    exact (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr heq))).mpr (hb z hz)

/-- Removability and a uniform bound on the entire larger closed disc. The
constants depend only on ε,a,M and precede the generic probability law. -/
theorem exists_uniform_renewal_removable_difference (ε a M : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hM : 0 < M) :
    ∃ ρ B : ℝ, 0 < ρ ∧ 0 < B ∧ 1 + ρ < Real.exp (a / 2) ∧
      ∀ p : ℕ → ℝ, (∀ n, 0 ≤ p n) → (∑' n, p n) = 1 →
        ε ≤ p 2 → ε ≤ p 3 →
        Summable (fun n : ℕ => p n * Real.exp (a * (n : ℝ))) →
        (∑' n : ℕ, p n * Real.exp (a * (n : ℝ))) ≤ M →
        AnalyticOnNhd ℂ (renewalRemovableDifference p) (Metric.closedBall 0 (1 + ρ)) ∧
        (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → ‖renewalRemovableDifference p z‖ ≤ B) ∧
        (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → z ≠ 1 →
          renewalRemovableDifference p z = (1 - renewalGenerating p z)⁻¹ -
            ((renewalMean p : ℂ) * (1 - z))⁻¹) := by
  have hR : 1 < Real.exp (a / 2) := Real.one_lt_exp_iff.mpr (half_pos ha)
  obtain ⟨C, h, hC, hh, hhR, hnear⟩ := exists_uniform_renewal_near_one ε a M hε ha hM
  obtain ⟨ρ, κ, hρ, hκ, _, hρh, hann⟩ :=
    exists_uniform_annular_deficit_of_exponential_moment ε h a M hε hh ha hM
  obtain ⟨K, D, _, _, hmoment⟩ := exists_renewal_moment_bounds a M ha hM
  have hρR : 1 + ρ < Real.exp (a / 2) := by linarith
  let Bnear := C / ((5 * ε) * (5 * ε / 2))
  let Baway := κ⁻¹ + ((5 * ε) * (2 * h))⁻¹
  have hBn : 0 < Bnear := by dsimp [Bnear]; positivity
  have hBa : 0 < Baway := by dsimp [Baway]; positivity
  refine ⟨ρ, Bnear + Baway, hρ, add_pos hBn hBa, hρR, ?_⟩
  intro p hp ht h2 h3 hs hm
  obtain ⟨hsp, hsR, hf, _, _, _⟩ := hmoment p hp hs hm
  obtain ⟨hg, _hg1, hmean, hrem, hlower⟩ := hnear p hp ht h2 h3 hs hm
  have hmpos : 0 < renewalMean p := lt_of_lt_of_le (by positivity : 0 < 5 * ε) hmean
  have hmne : (renewalMean p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hmpos.ne'
  have hg1 : AnalyticAt ℂ (renewalDividedDifference p) 1 := hg 1 (by simpa using hR)
  have hgn (z : ℂ) (hz : ‖z‖ ≤ 1 + ρ) : renewalDividedDifference p z ≠ 0 := by
    by_cases hzn : ‖z - 1‖ ≤ 2 * h
    · intro heq
      have hb := hlower z hzn
      rw [heq, norm_zero] at hb
      linarith
    · have hb := hann p hp ht h2 h3 hs hm z hz (le_of_lt (lt_of_not_ge hzn))
      change κ ≤ ‖1 - renewalGenerating p z‖ at hb
      rw [renewal_deficit_factorization p hp hsp ht hR.le hsR hf (hz.trans hρR.le)] at hb
      intro heq
      rw [heq, mul_zero, norm_zero] at hb
      exact hκ.not_ge hb
  have heq (z : ℂ) (hz : ‖z‖ ≤ 1 + ρ) (hz1 : z ≠ 1) :=
    renewalRemovableDifference_eq p hp hsp ht hR.le hsR hf (hz.trans hρR.le) hz1 hmpos.ne' (hgn z hz)
  refine ⟨?_, ?_, heq⟩
  · intro z hz
    have hz' : ‖z‖ ≤ 1 + ρ := by simpa using hz
    have hgz := hg z (by simpa using (hz'.trans_lt hρR))
    exact (analyticAt_renewal_dslope hgz hg1).fun_div
      (analyticAt_const.mul hgz) (mul_ne_zero hmne (hgn z hz'))
  · intro z hz
    by_cases hzn : ‖z - 1‖ ≤ 2 * h
    · have hb := norm_renewal_dslope_le hR hC.le hrem (hz.trans hρR.le)
      have hden : (5 * ε) * (5 * ε / 2) ≤
          ‖(renewalMean p : ℂ) * renewalDividedDifference p z‖ := by
        rw [norm_mul, Complex.norm_of_nonneg hmpos.le]
        exact mul_le_mul hmean (hlower z hzn) (by positivity) hmpos.le
      have hb' : ‖renewalRemovableDifference p z‖ ≤ Bnear := by
        rw [renewalRemovableDifference, norm_div]
        exact (div_le_div_of_nonneg_right hb (norm_nonneg _)).trans
          (div_le_div_of_nonneg_left hC.le (by positivity) hden)
      exact hb'.trans (le_add_of_nonneg_right hBa.le)
    · have hz1 : z ≠ 1 := by intro he; simp [he, hh.le] at hzn
      have haway : 2 * h ≤ ‖z - 1‖ := le_of_lt (lt_of_not_ge hzn)
      have hb := hann p hp ht h2 h3 hs hm z hz haway
      change κ ≤ ‖1 - renewalGenerating p z‖ at hb
      have hden : (5 * ε) * (2 * h) ≤ ‖(renewalMean p : ℂ) * (1 - z)‖ := by
        rw [norm_mul, Complex.norm_of_nonneg hmpos.le, norm_sub_rev]
        exact mul_le_mul hmean haway (by positivity) hmpos.le
      have hb' : ‖renewalRemovableDifference p z‖ ≤ Baway := by
        rw [heq z hz hz1]
        apply (norm_sub_le _ _).trans
        rw [norm_inv, norm_inv]
        exact add_le_add (inv_anti₀ hκ hb) (inv_anti₀ (by positivity) hden)
      exact hb'.trans (le_add_of_nonneg_left hBn.le)

end EinsteinFull.Work.W5
