import EinsteinFull.Blueprint.G1.node_rt_u3A_renewal_u23_cauchy
import EinsteinFull.Blueprint.G1.node_rt_u3A_renewal_u23_zero_u2D_exclusion
import Mathlib.Analysis.Complex.Liouville

open MeasureTheory Metric
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

open EinsteinRelation EinsteinFull.Work.W5

private theorem analyticAt_dslope_of_analytic {f : ℂ → ℂ} {z : ℂ}
    (hz : AnalyticAt ℂ f z) (h1 : AnalyticAt ℂ f 1) :
    AnalyticAt ℂ (dslope f 1) z := by
  by_cases he : z = 1
  · subst z
    obtain ⟨s, hs⟩ := h1
    exact ⟨s.fslope, hs.has_fpower_series_dslope_fslope⟩
  · have hq : AnalyticAt ℂ (fun w : ℂ => (f w - f 1) / (w - 1)) z :=
      (hz.sub analyticAt_const).fun_div (analyticAt_id.sub analyticAt_const)
        (sub_ne_zero.mpr he)
    have hs : slope f 1 = (fun w : ℂ => (f w - f 1) / (w - 1)) := by
      funext w
      exact slope_def_field _ _ _
    rw [← hs] at hq
    exact hq.congr (dslope_eventuallyEq_slope_of_ne _ he).symm

private theorem norm_generating_le_radius (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable p) (ht : ∑' n, p n = 1) (h0 : p 0 = 0)
    {z : ℂ} (hz : ‖z‖ ≤ 1) : ‖renewalGenerating p z‖ ≤ ‖z‖ := by
  have hn := summable_norm_generating_series p hp hs hz
  calc
    _ ≤ ∑' n : ℕ, ‖(p n : ℂ) * z ^ n‖ := norm_tsum_le_tsum_norm hn
    _ ≤ ∑' n : ℕ, p n * ‖z‖ := by
      apply hn.tsum_le_tsum _ (hs.mul_right _)
      intro n
      rw [norm_mul, Complex.norm_of_nonneg (hp n), norm_pow]
      cases n with
      | zero => simp [h0]
      | succ n =>
        apply mul_le_mul_of_nonneg_left _ (hp _)
        rw [pow_succ]
        exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz)
    _ = ‖z‖ := by rw [tsum_mul_right, ht, one_mul]

private theorem hasSum_centered_of_zero_mass (p : ℕ → ℝ) (hp : ∀ n, 0 ≤ p n)
    (hs : Summable p) (ht : ∑' n, p n = 1) (h0 : p 0 = 0)
    {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ =>
      ((renewalCoefficient p n : ℂ) - (renewalMean p : ℂ)⁻¹) * z ^ n)
      ((1 - renewalGenerating p z)⁻¹ - ((renewalMean p : ℂ) * (1 - z))⁻¹) := by
  have hr : ‖(‖z‖ : ℂ)‖ ≤ 1 := by simpa using hz.le
  have hrad := (norm_generating_le_radius p hp hs ht h0 hr).trans_lt
    (show ‖(‖z‖ : ℂ)‖ < 1 by simpa using hz)
  have hd : Summable (fun jn : ℕ × ℕ =>
      ‖(latticeConvolutionPower p jn.1 jn.2 : ℂ) * z ^ jn.2‖) := by
    apply (summable_prod_of_nonneg (fun _ => norm_nonneg _)).mpr
    refine ⟨fun j => (latticeConvolutionPower_generating_series p hp hs hz.le j).1, ?_⟩
    have he (j : ℕ) : (∑' n : ℕ, ‖(latticeConvolutionPower p j n : ℂ) * z ^ n‖) =
        (∑' n : ℕ, p n * ‖z‖ ^ n) ^ j := by
      have H := (latticeConvolutionPower_generating_series p hp hs hr j).2
      simp only [← Complex.ofReal_pow, ← Complex.ofReal_mul, ← Complex.ofReal_tsum] at H
      have H' := Complex.hasSum_ofReal.mp H
      simpa only [norm_mul, Complex.norm_of_nonneg (latticeConvolutionPower_nonneg p hp j _),
        norm_pow] using H'.tsum_eq
    simp_rw [he]
    apply summable_geometric_of_abs_lt_one
    simpa only [renewalGenerating, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
      ← Complex.ofReal_tsum, Complex.norm_real, Real.norm_eq_abs] using hrad
  have hd' := hd.of_norm
  have hu : HasSum (fun n : ℕ => (renewalCoefficient p n : ℂ) * z ^ n)
      (1 - renewalGenerating p z)⁻¹ := by
    rw [show (fun n : ℕ => (renewalCoefficient p n : ℂ) * z ^ n) =
        (fun n : ℕ => ∑' j : ℕ, (latticeConvolutionPower p j n : ℂ) * z ^ n) by
      funext n
      rw [renewalCoefficient, Complex.ofReal_tsum, tsum_mul_right]]
    apply hd'.prod_symm.prod.hasSum_iff.mpr
    change (∑' n : ℕ, ∑' j : ℕ, (latticeConvolutionPower p j n : ℂ) * z ^ n) = _
    rw [Summable.tsum_comm (f := fun j n : ℕ =>
      (latticeConvolutionPower p j n : ℂ) * z ^ n) hd']
    simp_rw [(latticeConvolutionPower_generating_series p hp hs hz.le _).2.tsum_eq]
    exact (hasSum_geometric_of_norm_lt_one
      ((norm_generating_le_radius p hp hs ht h0 hz.le).trans_lt hz)).tsum_eq
  have hg := (hasSum_geometric_of_norm_lt_one hz).mul_left (renewalMean p : ℂ)⁻¹
  convert hu.sub hg using 1
  · funext n
    exact sub_mul _ _ _
  · simp only [mul_inv_rev]
    ring

/-- Cauchy's estimate for the actual removable renewal resolvent, using exactly
its zero-exclusion dependency (`paper/main.tex:386–391`). -/
theorem node_rt_u3A_renewal_u23_cauchy_of_deps
    (hzero : node_rt_u3A_renewal_u23_zero_u2D_exclusionStmt) :
    node_rt_u3A_renewal_u23_cauchyStmt := by
  intro d hd Λ₀ r₀
  obtain ⟨l₀, hl₀, hr₀, hzero⟩ := hzero d hd Λ₀ r₀
  refine ⟨l₀, hl₀, hr₀, ?_⟩
  intro l hl δ hδ hδ1
  obtain ⟨ρ, h, κ, B, hρ, hh, hκ, hB, hzero⟩ := hzero l hl δ hδ hδ1
  let D := B / (ρ / 4)
  let A := D / 2 + κ⁻¹ + (4 * h)⁻¹
  have hDpos : 0 < D := div_pos hB (by positivity)
  have hA : 0 < A := by dsimp [A]; positivity
  let R := 1 + ρ / 4
  have hR1 : 1 < R := by dsimp [R]; linarith
  have hR : 0 < R := zero_lt_one.trans hR1
  refine ⟨ρ / 2, A, Real.log R, A, half_pos hρ, hA, Real.log_pos hR1, hA, ?_⟩
  intro Q lam h₀ h₁ P K hK hD
  obtain ⟨hm, hmB, hf, hg, hg1, _hf1, hb, hfac, hnear, haway, _hzeros⟩ :=
    hzero Q lam h₀ h₁ P K hK hD
  let p := regenerationLatticeMass hd Q lam l K hK.1 hD
  change 2 ≤ renewalMean p at hm
  change renewalDividedDifference p 1 = (renewalMean p : ℂ) at hg1
  change ∀ z : ℂ, ‖z‖ ≤ 1 + ρ →
    1 - renewalGenerating p z = (1 - z) * renewalDividedDifference p z at hfac
  have hmpos : 0 < renewalMean p := by linarith
  have hmne : (renewalMean p : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hmpos.ne'
  have hone : (1 : ℂ) ∈ closedBall 0 (1 + 2 * ρ) := by simp; linarith
  have hfOne : renewalGenerating p 1 = 1 := by
    have H := hfac 1 (by simp; linarith)
    exact (sub_eq_zero.mp (by simpa using H)).symm
  have hnz (z : ℂ) (hz : ‖z‖ ≤ 1 + ρ) : renewalDividedDifference p z ≠ 0 := by
    by_cases hn : ‖z - 1‖ ≤ 2 * h
    · intro he
      have H := hnear z hz hn
      rw [he, norm_zero] at H
      linarith
    · intro he
      have H := haway z hz (le_of_not_ge hn)
      rw [hfac z hz, he, mul_zero, norm_zero] at H
      exact hκ.not_ge H
  have hEq (z : ℂ) (hz : ‖z‖ ≤ 1 + ρ) (hz1 : z ≠ 1) :
      renewalRemovableDifference p z = (1 - renewalGenerating p z)⁻¹ -
        ((renewalMean p : ℂ) * (1 - z))⁻¹ := by
    rw [renewalRemovableDifference, dslope_of_ne _ hz1, slope_def_field, hg1, hfac z hz]
    have hz' := sub_ne_zero.mpr hz1
    have hz'' := sub_ne_zero.mpr (Ne.symm hz1)
    have hgn := hnz z hz
    field_simp
    ring
  have hgBound (z : ℂ) (hz : ‖z‖ ≤ 1 + ρ) : ‖renewalDividedDifference p z‖ ≤ B := by
    by_cases he : z = 1
    · rw [he, hg1, Complex.norm_of_nonneg hmpos.le]
      exact hmB
    · have H := Convex.norm_image_sub_le_of_norm_deriv_le
        (fun w hw => (hf w hw).differentiableAt)
        (fun w hw => (le_add_of_nonneg_left (norm_nonneg _)).trans
          ((le_add_of_nonneg_right (norm_nonneg _)).trans (hb w (by simpa using hw))))
        (convex_closedBall (0 : ℂ) (1 + 2 * ρ)) hone
        (show z ∈ closedBall 0 (1 + 2 * ρ) by simpa using (show ‖z‖ ≤ 1 + 2 * ρ by linarith))
      rw [hfOne, ← norm_sub_rev, hfac z hz, norm_mul, norm_sub_rev] at H
      rw [mul_comm B] at H
      exact (mul_le_mul_iff_right₀ (norm_pos_iff.mpr (sub_ne_zero.mpr he))).mp H
  have hgDeriv (z : ℂ) (hz : ‖z‖ ≤ 1 + ρ / 2) :
      ‖deriv (renewalDividedDifference p) z‖ ≤ D := by
    have hsub : closedBall z (ρ / 4) ⊆ ball 0 (1 + 2 * ρ) := by
      intro w hw
      have hwz : ‖w - z‖ ≤ ρ / 4 := by
        rw [← dist_eq_norm]
        exact Metric.mem_closedBall.mp hw
      have H := norm_add_le (w - z) z
      rw [sub_add_cancel] at H
      simpa using (show ‖w‖ < 1 + 2 * ρ by linarith)
    apply Complex.norm_deriv_le_of_forall_mem_sphere_norm_le (by positivity)
      (hg.differentiableOn.diffContOnCl_ball (fun w hw => ball_subset_closedBall (hsub hw)))
    intro w hw
    have hwz : ‖w - z‖ = ρ / 4 := by simpa using hw
    have H := norm_add_le (w - z) z
    rw [sub_add_cancel] at H
    exact hgBound w (by linarith)
  have hslope (z : ℂ) (hz : ‖z‖ ≤ 1 + ρ / 2) :
      ‖dslope (renewalDividedDifference p) 1 z‖ ≤ D := by
    by_cases he : z = 1
    · rw [he, dslope_same]
      exact hgDeriv 1 (by simp; linarith)
    · rw [dslope_of_ne _ he, slope_def_field, norm_div]
      apply (div_le_iff₀ (norm_pos_iff.mpr (sub_ne_zero.mpr he))).mpr
      apply Convex.norm_image_sub_le_of_norm_deriv_le
        (fun w hw => (hg w (by
          have : ‖w‖ ≤ 1 + ρ / 2 := by simpa using hw
          simpa using (show ‖w‖ ≤ 1 + 2 * ρ by linarith))).differentiableAt)
        (fun w hw => hgDeriv w (by simpa using hw))
        (convex_closedBall (0 : ℂ) (1 + ρ / 2))
        (by simp; linarith) (by simpa using hz)
  have hVa : AnalyticOnNhd ℂ (renewalRemovableDifference p) (closedBall 0 (1 + ρ / 2)) := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 + ρ / 2 := by simpa using hz
    have hgz := hg z (by simpa using (show ‖z‖ ≤ 1 + 2 * ρ by linarith))
    exact (analyticAt_dslope_of_analytic hgz (hg 1 hone)).fun_div
      (analyticAt_const.mul hgz) (mul_ne_zero hmne (hnz z (by linarith)))
  have hVb (z : ℂ) (hz : ‖z‖ ≤ 1 + ρ / 2) : ‖renewalRemovableDifference p z‖ ≤ A := by
    by_cases hn : ‖z - 1‖ ≤ 2 * h
    · have hden : 2 ≤ ‖(renewalMean p : ℂ) * renewalDividedDifference p z‖ := by
        rw [norm_mul, Complex.norm_of_nonneg hmpos.le]
        exact (by nlinarith only [hm, hnear z (by linarith) hn])
      have H : ‖renewalRemovableDifference p z‖ ≤ D / 2 := by
        rw [renewalRemovableDifference, norm_div]
        exact (div_le_div_of_nonneg_right (hslope z hz) (norm_nonneg _)).trans
          (div_le_div_of_nonneg_left hDpos.le (by norm_num) hden)
      exact H.trans (by
        dsimp [A]
        have hk : 0 < κ⁻¹ := inv_pos.mpr hκ
        have hhinv : 0 < (4 * h)⁻¹ := inv_pos.mpr (mul_pos (by norm_num) hh)
        linarith only [hk, hhinv])
    · have hz1 : z ≠ 1 := by intro he; simp [he, hh.le] at hn
      have ha := haway z (by linarith) (le_of_not_ge hn)
      have hden : 4 * h ≤ ‖(renewalMean p : ℂ) * (1 - z)‖ := by
        rw [norm_mul, Complex.norm_of_nonneg hmpos.le, norm_sub_rev]
        nlinarith only [hm, le_of_not_ge hn, hh]
      rw [hEq z (by linarith) hz1]
      apply (norm_sub_le _ _).trans
      rw [norm_inv, norm_inv]
      exact (add_le_add (inv_anti₀ hκ ha) (inv_anti₀ (by positivity) hden)).trans
        (by dsimp [A]; linarith)
  refine ⟨hVa, hVb, fun z hz hz1 => hEq z (by linarith) hz1, ?_⟩
  have hp : ∀ n, 0 ≤ p n := regenerationLatticeMass_nonneg hd Q lam l K hK.1 hD
  have ht : ∑' n, p n = 1 := by
    have H : ((∑' n, p n : ℝ) : ℂ) = 1 := by
      simpa only [renewalGenerating, one_pow, mul_one, ← Complex.ofReal_tsum] using hfOne
    exact_mod_cast H
  have hs : Summable p := by
    by_contra hn
    have H := tsum_eq_zero_of_not_summable hn
    rw [ht] at H
    exact one_ne_zero H
  have hp0 : p 0 = 0 := regenerationLatticeMass_eq_zero_of_lt_two hd Q lam l h₀
    (hl₀.trans_le hl) K hK.1 hD 0 (by norm_num)
  have hAt : HasFPowerSeriesAt (renewalRemovableDifference p) (renewalCenteredSeries p) 0 := by
    apply hasFPowerSeriesAt_iff.mpr
    filter_upwards [isOpen_ball.mem_nhds (mem_ball_self zero_lt_one : (0 : ℂ) ∈ ball 0 1)] with z hz
    have hz' : ‖z‖ < 1 := by simpa using hz
    have hz1 : z ≠ 1 := by intro he; simp [he] at hz'
    have H := hasSum_centered_of_zero_mass p hp hs ht hp0 hz'
    rw [← hEq z (by linarith) hz1] at H
    simpa only [renewalCenteredSeries, FormalMultilinearSeries.coeff_ofScalars,
      zero_add, smul_eq_mul, mul_comm] using H
  let r : ℝ≥0 := ⟨R, hR.le⟩
  have hc := (hVa.differentiableOn.mono
    (closedBall_subset_closedBall (show R ≤ 1 + ρ / 2 by dsimp [R]; linarith))).hasFPowerSeriesOnBall
      (show 0 < r from hR)
  have hseries := hAt.eq_formalMultilinearSeries hc.hasFPowerSeriesAt
  change renewalCenteredSeries p = cauchyPowerSeries (renewalRemovableDifference p) 0 R at hseries
  intro n
  have heq : (cauchyPowerSeries (renewalRemovableDifference p) 0 R).coeff n =
      ((renewalCoefficient p n : ℂ) - (renewalMean p : ℂ)⁻¹) := by
    rw [← hseries]
    exact FormalMultilinearSeries.coeff_ofScalars
  have hn := norm_cauchyPowerSeries_coeff_le hR
    (fun z hz => hVb z (by dsimp [R] at hz; linarith)) n
  rw [heq, ← Complex.ofReal_inv, ← Complex.ofReal_sub, Complex.norm_real] at hn
  calc
    |renewalCoefficient p n - (renewalMean p)⁻¹| ≤ A / R ^ n := hn
    _ = A * Real.exp (-Real.log R * (n : ℝ)) := by
      rw [neg_mul, Real.exp_neg, mul_comm (Real.log R) (n : ℝ),
        Real.exp_nat_mul, Real.exp_log hR, div_eq_mul_inv]

end EinsteinFull.Blueprint
