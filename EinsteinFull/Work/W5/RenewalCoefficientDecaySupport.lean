import EinsteinFull.Work.W5.RenewalNearOneSupport
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.OfScalars

/-!
# Cauchy estimates for the literal renewal coefficients

The interior absolutely convergent convolution series identifies the coefficients
of the removable renewal difference. Uniqueness transports this identification
to the larger disc, where Cauchy's estimate gives a uniform exponential rate.
All laws below are generic mass sequences; no regeneration-law claim is made.
-/

open Metric
open scoped Topology NNReal

noncomputable section

namespace EinsteinFull.Work.W5

/-- The actual renewal coefficient, including all cycle counts. -/
def renewalCoefficient (p : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑' j : ℕ, latticeConvolutionPower p j n

/-- A positive mass at two already excludes unit mass at zero. -/
theorem renewal_mass_zero_lt_one (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable p) (ht : ∑' n, p n = 1) (h2 : 0 < p 2) : p 0 < 1 := by
  have h := norm_generating_series_lt_one p hp hs ht h2 (z := 0) (by simp)
  have heq : (∑' n : ℕ, (p n : ℂ) * (0 : ℂ) ^ n) = (p 0 : ℂ) := by
    rw [tsum_eq_single 0 (fun n hn => by simp [hn])]
    simp
  rwa [heq, Complex.norm_of_nonneg (hp 0)] at h

/-- The zeroth time coefficient of each convolution power includes the mass at
zero; it need not vanish for positive cycle count. -/
theorem latticeConvolutionPower_zero_right (p : ℕ → ℝ) (j : ℕ) :
    latticeConvolutionPower p j 0 = p 0 ^ j := by
  induction j with
  | zero => simp [latticeConvolutionPower]
  | succ j ih => simp [latticeConvolutionPower, ih, pow_succ, mul_comm]

/-- The full zeroth renewal coefficient is the convergent geometric sum,
including the case of nonzero mass at zero. -/
theorem renewalCoefficient_zero (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable p) (ht : ∑' n, p n = 1) (h2 : 0 < p 2) :
    renewalCoefficient p 0 = (1 - p 0)⁻¹ := by
  simp only [renewalCoefficient, latticeConvolutionPower_zero_right]
  exact (hasSum_geometric_of_lt_one (hp 0) (renewal_mass_zero_lt_one p hp hs ht h2)).tsum_eq

/-- The scalar power series of the centered literal renewal coefficients. -/
def renewalCenteredSeries (p : ℕ → ℝ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  FormalMultilinearSeries.ofScalars ℂ
    (fun n => (renewalCoefficient p n : ℂ) - (renewalMean p : ℂ)⁻¹)

/-- The interior series identity follows by subtraction of two convergent
series; the convolution interchange is the absolute-summability bridge. -/
theorem hasSum_centered_renewal_generating_series (p : ℕ → ℝ)
    (hp : ∀ n, 0 ≤ p n) (hs : Summable p) (ht : ∑' n, p n = 1)
    (h2 : 0 < p 2) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ =>
      ((renewalCoefficient p n : ℂ) - (renewalMean p : ℂ)⁻¹) * z ^ n)
      ((1 - renewalGenerating p z)⁻¹ - ((renewalMean p : ℂ) * (1 - z))⁻¹) := by
  have hu := hasSum_renewal_generating_series p hp hs ht h2 hz
  have hg := (hasSum_geometric_of_norm_lt_one hz).mul_left (renewalMean p : ℂ)⁻¹
  convert hu.sub hg using 1
  · funext n
    simp only [renewalCoefficient, sub_mul]
  · simp only [renewalGenerating, mul_inv_rev]
    ring

/-- Cauchy's coefficient estimate, stated directly for the scalar coefficients
of Mathlib's circle-integral series. No analyticity assumption is needed here. -/
theorem norm_cauchyPowerSeries_coeff_le {f : ℂ → ℂ} {R B : ℝ}
    (hR : 0 < R) (hb : ∀ z : ℂ, ‖z‖ = R → ‖f z‖ ≤ B) (n : ℕ) :
    ‖(cauchyPowerSeries f 0 R).coeff n‖ ≤ B / R ^ n := by
  have hi : ∀ z ∈ sphere (0 : ℂ) R,
      ‖(1 / (z - 0)) ^ n • (z - 0)⁻¹ • f z‖ ≤ B / (R ^ n * R) := by
    intro z hz
    have hz' : ‖z‖ = R := by simpa using hz
    simp only [sub_zero, one_div, norm_smul, norm_pow, norm_inv, hz']
    calc
      R⁻¹ ^ n * (R⁻¹ * ‖f z‖) ≤ R⁻¹ ^ n * (R⁻¹ * B) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hb z hz') (inv_nonneg.mpr hR.le))
          (pow_nonneg (inv_nonneg.mpr hR.le) n)
      _ = B / (R ^ n * R) := by rw [div_eq_mul_inv, mul_inv, inv_pow]; ring
  change ‖cauchyPowerSeries f 0 R n (fun _ => 1)‖ ≤ _
  rw [cauchyPowerSeries_apply]
  apply (circleIntegral.norm_two_pi_i_inv_smul_integral_le_of_norm_le_const hR.le hi).trans_eq
  field_simp

/-- The uniform exponential renewal estimate for a generic probability sequence.
The constants precede the law and the coefficient index. Zero and one are
retained, and no coefficient identification or analytic premise is assumed. -/
theorem exists_uniform_renewal_coefficient_decay (ε a M : ℝ)
    (hε : 0 < ε) (ha : 0 < a) (hM : 0 < M) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
      ∀ p : ℕ → ℝ, (∀ n, 0 ≤ p n) → (∑' n, p n) = 1 →
        ε ≤ p 2 → ε ≤ p 3 →
        Summable (fun n : ℕ => p n * Real.exp (a * (n : ℝ))) →
        (∑' n : ℕ, p n * Real.exp (a * (n : ℝ))) ≤ M →
        ∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower p j n) - (renewalMean p)⁻¹| ≤
          C * Real.exp (-c * (n : ℝ)) := by
  obtain ⟨ρ, B, hρ, hB, _, hV⟩ :=
    exists_uniform_renewal_removable_difference ε a M hε ha hM
  let R : ℝ := 1 + ρ / 2
  have hR1 : 1 < R := by dsimp [R]; linarith
  have hR : 0 < R := lt_trans zero_lt_one hR1
  have hRρ : R ≤ 1 + ρ := by dsimp [R]; linarith
  refine ⟨Real.log R, B, Real.log_pos hR1, hB, ?_⟩
  intro p hp ht h2 h3 hs hm
  obtain ⟨hVa, hVb, hVe⟩ := hV p hp ht h2 h3 hs hm
  obtain ⟨K, D, _, _, hmoment⟩ := exists_renewal_moment_bounds a M ha hM
  obtain ⟨hsp, _, _, _, _, _⟩ := hmoment p hp hs hm
  have hAt : HasFPowerSeriesAt (renewalRemovableDifference p) (renewalCenteredSeries p) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self zero_lt_one : (0 : ℂ) ∈ ball 0 1)] with z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    have hz1 : z ≠ 1 := by intro he; simp [he] at hz'
    have hsum := hasSum_centered_renewal_generating_series p hp hsp ht
      (lt_of_lt_of_le hε h2) hz'
    rw [← hVe z (by linarith) hz1] at hsum
    simpa only [renewalCenteredSeries, FormalMultilinearSeries.coeff_ofScalars,
      zero_add, smul_eq_mul, mul_comm] using hsum
  let r : ℝ≥0 := ⟨R, hR.le⟩
  have hd : DifferentiableOn ℂ (renewalRemovableDifference p) (closedBall 0 (r : ℝ)) := by
    apply hVa.differentiableOn.mono
    intro z hz
    exact closedBall_subset_closedBall hRρ hz
  have hc := hd.hasFPowerSeriesOnBall (show 0 < r from hR)
  have hseries := hAt.eq_formalMultilinearSeries hc.hasFPowerSeriesAt
  change renewalCenteredSeries p = cauchyPowerSeries (renewalRemovableDifference p) 0 R at hseries
  intro n
  have heq : (cauchyPowerSeries (renewalRemovableDifference p) 0 R).coeff n =
      ((renewalCoefficient p n : ℂ) - (renewalMean p : ℂ)⁻¹) := by
    rw [← hseries]
    exact FormalMultilinearSeries.coeff_ofScalars
  have hn := norm_cauchyPowerSeries_coeff_le hR
    (fun z hz => hVb z (hz.le.trans hRρ)) n
  rw [heq, ← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.norm_real] at hn
  calc
    |renewalCoefficient p n - (renewalMean p)⁻¹| ≤ B / R ^ n := hn
    _ = B * Real.exp (-Real.log R * (n : ℝ)) := by
      rw [neg_mul, Real.exp_neg, mul_comm (Real.log R) (n : ℝ),
        Real.exp_nat_mul, Real.exp_log hR, div_eq_mul_inv]

end EinsteinFull.Work.W5
