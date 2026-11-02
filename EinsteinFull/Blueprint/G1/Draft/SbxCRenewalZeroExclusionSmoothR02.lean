import EinsteinFull.Blueprint.G1.Draft.S3SmoothScope
import EinsteinFull.Blueprint.G1.Proofs.W1Reduction1
import Mathlib.Analysis.Complex.Liouville

/-! Draft smooth-law renewal estimates, conditional on the two source inputs. -/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint.SbxCRenewalZeroExclusionR02
open EinsteinRelation EinsteinFull.Work.W5

def twoMassesSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ ε : ℝ, 0 < ε ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    let p := regenerationLatticeMass hd Q lam l K hK.1 hD
    ε ≤ p 2 ∧ ε ≤ p 3


def firstCycleTailsSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C a M : ℝ, 0 < c ∧ 0 < C ∧ 0 < a ∧ a < c ∧ 0 < M ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    ∃ hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0,
      ENNReal.ofReal (1 / 2 : ℝ) ≤ Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ∧
      (∀ t : ℝ, 0 ≤ t → Regeneration.annealedCoupledLaw Q.measure K
        {ωz | ENNReal.ofReal t < regenerationTime hd lam l 1 ωz.2} ≤
          ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t))) ∧
      (∫⁻ ωz, Work.W5.regenerationExponentialWeight hd lam l a 1 ωz.2
        ∂Regeneration.annealedCoupledLaw Q.measure K) ≤ ENNReal.ofReal M ∧
      (∫⁻ ωz, Work.W5.regenerationExponentialWeight hd lam l a 1 ωz.2
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal M


def zeroExclusionSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ ρ h κ B : ℝ, 0 < ρ ∧ 0 < h ∧ 0 < κ ∧ 0 < B ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    let p := regenerationLatticeMass hd Q lam l K hK.1 hD
    let f := renewalGenerating p
    let g := renewalDividedDifference p
    let m := renewalMean p
    2 ≤ m ∧ m ≤ B ∧
    AnalyticOnNhd ℂ f (Metric.closedBall 0 (1 + 2 * ρ)) ∧
    AnalyticOnNhd ℂ g (Metric.closedBall 0 (1 + 2 * ρ)) ∧
    g 1 = (m : ℂ) ∧ HasDerivAt f (m : ℂ) 1 ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + 2 * ρ →
      ‖f z‖ + ‖deriv f z‖ + ‖iteratedDeriv 2 f z‖ ≤ B) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → 1 - f z = (1 - z) * g z) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → ‖z - 1‖ ≤ 2 * h → 1 ≤ ‖g z‖) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → 2 * h ≤ ‖z - 1‖ → κ ≤ ‖1 - f z‖) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → (1 - f z = 0 ↔ z = 1))


/-- Uniform zero exclusion for the actual first-cycle law, conditional on
its two-mass and first-cycle tail estimates. -/
theorem smoothZeroExclusion_of_deps
    (hmasses : twoMassesSmoothStmt)
    (htails : firstCycleTailsSmoothStmt) :
    zeroExclusionSmoothStmt := by
  intro d hd D
  obtain ⟨lm, hlm, hrm, hmasses⟩ := hmasses d hd D
  obtain ⟨lt, hlt, _hrt, htails⟩ := htails d hd D
  refine ⟨max lm lt, lt_of_lt_of_le hlm (le_max_left _ _),
    hrm.trans_le (mul_le_mul_of_nonneg_left (le_max_left _ _) (by norm_num)), ?_⟩
  intro l hl δ hδ hδ1
  obtain ⟨ε, hε, hmasses⟩ := hmasses l ((le_max_left _ _).trans hl) δ hδ hδ1
  obtain ⟨c, C₀, a, M, _hc, _hC₀, ha, _hac, hM, htails⟩ :=
    htails l ((le_max_right _ _).trans hl) δ hδ hδ1
  obtain ⟨K₀, C, hK₀, hC, hmoment⟩ := exists_renewal_moment_bounds a M ha hM
  let R := Real.exp (a / 2)
  have hR : 1 < R := Real.one_lt_exp_iff.mpr (half_pos ha)
  let b := (R - 1) / 8
  have hb : 0 < b := div_pos (sub_pos.mpr hR) (by norm_num)
  let h := 1 / (2 * C)
  have hh : 0 < h := by dsimp [h]; positivity
  have hCh : C * (2 * h) = 1 := by dsimp [h]; field_simp
  obtain ⟨r, κ, hr, hκ, _hrR, _hrh, hann⟩ :=
    exists_uniform_annular_deficit_of_exponential_moment ε h a M hε hh ha hM
  let ρ := min r b
  have hρ : 0 < ρ := lt_min hr hb
  have hρr : ρ ≤ r := min_le_left _ _
  have hρb : ρ ≤ b := min_le_right _ _
  have hdisc : 1 + 2 * ρ + b < R := by dsimp [b] at hb hρb ⊢; linarith
  let B := K₀ + M + M / b + 2 * M / b ^ 2 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  refine ⟨ρ, h, κ, B, hρ, hh, hκ, hB, ?_⟩
  intro Q hQ lam h₀ h₁ P K hK hD
  obtain ⟨hD', _hhalf, _htail, _hannMoment, hcond⟩ := htails Q hQ lam h₀ h₁ P K hK
  have hcond' : (∫⁻ ωz, regenerationExponentialWeight hd lam l a 1 ωz.2
      ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal M := hcond
  have hfinite := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hcond'
  let p := regenerationLatticeMass hd Q lam l K hK.1 hD
  have hp : ∀ n, 0 ≤ p n := regenerationLatticeMass_nonneg hd Q lam l K hK.1 hD
  have hnorm := regenerationLatticeMass_hasSum_of_exponentialMoment
    hd Q lam l a h₀.ne' K hK.1 hD hfinite
  have hexp := regenerationLatticeMass_exponential_hasSum
    hd Q lam l a h₀.ne' K hK.1 hD hfinite
  have hbound := regenerationLatticeMass_exponential_tsum_le
    hd Q lam l a M h₀.ne' hM.le K hK.1 hD hcond'
  obtain ⟨h2, h3⟩ := hmasses Q hQ lam h₀ h₁ P K hK hD
  obtain ⟨hs, hsR, hf, hfK, hss, hssC⟩ := hmoment p hp hexp.summable hbound
  have hmeanSum := summable_renewalMean p hp hR.le hf
  have hmean : 2 ≤ renewalMean p := by
    have hsmall (n : ℕ) (hn : n < 2) : p n = 0 :=
      regenerationLatticeMass_eq_zero_of_lt_two hd Q lam l h₀
        (lt_of_lt_of_le hlm ((le_max_left _ _).trans hl)) K hK.1 hD n hn
    have hterm (n : ℕ) : 2 * p n ≤ p n * (n : ℝ) := by
      by_cases hn : n < 2
      · rw [hsmall n hn]; simp
      · have hn' : (2 : ℝ) ≤ n := by exact_mod_cast (Nat.le_of_not_gt hn)
        nlinarith only [hp n, hn']
    have ht := (hs.mul_left 2).tsum_le_tsum hterm hmeanSum
    have hnorm' : ∑' n, p n = 1 := hnorm.tsum_eq
    simpa only [tsum_mul_left, hnorm', mul_one, renewalMean] using ht
  have hmeanK : renewalMean p ≤ K₀ := by
    exact (hmeanSum.tsum_le_tsum (fun n =>
      le_mul_of_one_le_right (mul_nonneg (hp n) (Nat.cast_nonneg n))
        (one_le_pow₀ hR.le)) hf).trans hfK
  have hfana := analyticOnNhd_renewalGenerating p hp hsR
  have hgana := analyticOnNhd_renewalDividedDifference p hp hR.le hf
  have hnormf (z : ℂ) (hz : ‖z‖ ≤ R) : ‖renewalGenerating p z‖ ≤ M := by
    have hsE : Summable (fun n : ℕ => p n * (Real.exp a) ^ n) := by
      simpa only [mul_comm a, Real.exp_nat_mul] using hexp.summable
    have hRE : R ≤ Real.exp a := Real.exp_le_exp.mpr (by linarith)
    have hzE := hz.trans hRE
    have hsum := summable_norm_generating_series_of_radius p hp hsE hzE
    calc
      ‖renewalGenerating p z‖ ≤ ∑' n : ℕ, ‖(p n : ℂ) * z ^ n‖ := norm_tsum_le_tsum_norm hsum
      _ ≤ ∑' n : ℕ, p n * Real.exp (a * n) := by
        apply hsum.tsum_le_tsum _ hexp.summable
        intro n
        rw [norm_mul, Complex.norm_of_nonneg (hp n), norm_pow]
        rw [mul_comm a, Real.exp_nat_mul]
        exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hzE n) (hp n)
      _ ≤ M := hbound
  have hderivs (z : ℂ) (hz : ‖z‖ ≤ 1 + 2 * ρ) :
      ‖deriv (renewalGenerating p) z‖ ≤ M / b ∧
      ‖iteratedDeriv 2 (renewalGenerating p) z‖ ≤ 2 * M / b ^ 2 := by
    have hsub : Metric.closedBall z b ⊆ Metric.ball 0 R := by
      intro w hw
      have hwz : ‖w - z‖ ≤ b := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
      have hw0 := norm_add_le (w - z) z
      rw [sub_add_cancel] at hw0
      simpa only [Metric.mem_ball, dist_zero_right] using (by linarith : ‖w‖ < R)
    have hdiff : DiffContOnCl ℂ (renewalGenerating p) (Metric.ball z b) :=
      hfana.differentiableOn.diffContOnCl_ball hsub
    have hsphere (w : ℂ) (hw : w ∈ Metric.sphere z b) : ‖renewalGenerating p w‖ ≤ M :=
      hnormf w (le_of_lt (by simpa using hsub (Metric.sphere_subset_closedBall hw)))
    constructor
    · simpa only [iteratedDeriv_one, Nat.factorial_one, Nat.cast_one, one_mul, pow_one] using
        Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 1 hb hdiff hsphere
    · have h := Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le 2 hb hdiff hsphere
      refine h.trans (le_of_eq ?_)
      norm_num
  have hclosed : Metric.closedBall (0 : ℂ) (1 + 2 * ρ) ⊆ Metric.ball 0 R := by
    intro z hz
    have hz' : ‖z‖ ≤ 1 + 2 * ρ := by simpa using hz
    simpa using (show ‖z‖ < R by linarith)
  have hfactor (z : ℂ) (hz : ‖z‖ ≤ 1 + ρ) :
      1 - renewalGenerating p z = (1 - z) * renewalDividedDifference p z :=
    renewal_deficit_factorization p hp hs hnorm.tsum_eq hR.le hsR hf
      (by linarith)
  have hnear (z : ℂ) (hz : ‖z‖ ≤ 1 + ρ) (hzone : ‖z - 1‖ ≤ 2 * h) :
      1 ≤ ‖renewalDividedDifference p z‖ := by
    have hrem := norm_renewalDividedDifference_sub_mean_le p hp hR.le hf hss hssC
      (z := z) (by linarith : ‖z‖ ≤ R)
    have hrem1 : ‖renewalDividedDifference p z - (renewalMean p : ℂ)‖ ≤ 1 :=
      hrem.trans (by nlinarith only [hzone, hC, hCh])
    have htri' := norm_add_le (renewalDividedDifference p z)
      ((renewalMean p : ℂ) - renewalDividedDifference p z)
    rw [add_sub_cancel, norm_sub_rev, Complex.norm_of_nonneg (by linarith)] at htri'
    linarith
  have hann' (z : ℂ) (hz : ‖z‖ ≤ 1 + ρ) (haway : 2 * h ≤ ‖z - 1‖) :
      κ ≤ ‖1 - renewalGenerating p z‖ :=
    hann p hp hnorm.tsum_eq h2 h3 hexp.summable hbound z (by linarith) haway
  refine ⟨hmean, ?_, hfana.mono hclosed, hgana.mono hclosed,
    renewalDividedDifference_one p,
    hasDerivAt_renewalGenerating_one p hp hs hnorm.tsum_eq hR hsR hf,
    ?_, hfactor, hnear, hann', ?_⟩
  · have hdiv : 0 ≤ M / b := div_nonneg hM.le hb.le
    have hdiv2 : 0 ≤ 2 * M / b ^ 2 := by positivity
    dsimp [B]
    linarith
  · intro z hz
    obtain ⟨hd1, hd2⟩ := hderivs z hz
    have hfM := hnormf z (by linarith)
    dsimp [B]
    linarith
  · intro z hz
    constructor
    · intro heq
      by_cases hn : ‖z - 1‖ ≤ 2 * h
      · have hg : renewalDividedDifference p z ≠ 0 := by
          intro hg
          have hb' := hnear z hz hn
          rw [hg, norm_zero] at hb'
          linarith
        have he := hfactor z hz
        rw [heq] at he
        exact (sub_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hg)).symm
      · have hb' := hann' z hz (le_of_lt (lt_of_not_ge hn))
        rw [heq, norm_zero] at hb'
        exact False.elim (hκ.not_ge hb')
    · rintro rfl
      simpa only [sub_self, zero_mul] using hfactor 1 (by simpa using hρ.le)


end EinsteinFull.Blueprint.SbxCRenewalZeroExclusionR02
