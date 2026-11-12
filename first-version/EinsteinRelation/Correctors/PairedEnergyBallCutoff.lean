import EinsteinRelation.Correctors.PrescribedBallCutoff

/-! # Uniform concentric-ball cutoffs for the paired energy

Source: `paper/main.tex:834–850`. A single Euclidean bump is dilated;
its derivative constant precedes the spatial scale.
-/

namespace EinsteinRelation.Correctors
open External.AKM

/-- Smooth nonnegative cutoffs equal one on the inner ball. Their squared
Euclidean gradient has a uniform inverse-square bound.
Source: `paper/main.tex:834–850`. -/
theorem exists_paired_energy_ball_cutoff (d : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ R : ℝ, 0 < R →
      ∃ χ : Vec d → ℝ, IsSpatialTest (originBall d (2*R)) χ ∧
        (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
        (∀ x ∈ originBall d R, χ x = 1) ∧
        ∀ x, euclideanSq (gradient χ x) ≤ (D/R)^2 := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    ⟨1, 3/2, by norm_num, by norm_num⟩
  let φ : Vec d → ℝ := b ∘ J
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := b.contDiff.comp J.contDiff
  have hc : HasCompactSupport φ := b.hasCompactSupport.comp_homeomorph J.toHomeomorph
  obtain ⟨N,hN⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hφ.continuous_fderiv (by simp))
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  have hs : tsupport φ ⊆ originBall d 2 := by
    intro x hx
    have heq := tsupport_comp_eq_preimage (b : EuclideanSpace ℝ (Fin d) → ℝ)
      J.toHomeomorph
    rw [b.tsupport_eq] at heq
    have hx' : J x ∈ Metric.closedBall 0 (3/2) := (Set.ext_iff.mp heq x).mp hx
    have hn : euclideanNorm x ≤ 3/2 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, J,
        PiLp.continuousLinearEquiv_symm_apply,
        ← TimeChange.euclideanNorm_eq_norm_toLp] using hx'
    change euclideanNorm x < 2
    linarith
  refine ⟨Real.sqrt (d : ℝ)*N, by positivity, ?_⟩
  intro R hR
  let χ : Vec d → ℝ := fun x => φ (R⁻¹ • x)
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ :=
    hφ.comp (contDiff_const.smul contDiff_id)
  have hχc : HasCompactSupport χ := hc.comp_smul (inv_ne_zero hR.ne')
  have hnorm (x : Vec d) : euclideanNorm (R⁻¹ • x) = euclideanNorm x / R := by
    rw [TimeChange.euclideanNorm_smul, abs_of_pos (inv_pos.mpr hR)]
    ring
  refine ⟨χ, ⟨hχ,hχc,?_⟩, (fun x => ⟨b.nonneg,b.le_one⟩), ?_, ?_⟩
  · intro x hx
    have heq := tsupport_comp_eq_preimage φ
      (Homeomorph.smulOfNeZero R⁻¹ (inv_ne_zero hR.ne'))
    have hx' : R⁻¹ • x ∈ tsupport φ := (Set.ext_iff.mp heq x).mp hx
    have hn : euclideanNorm (R⁻¹ • x) < 2 := hs hx'
    change euclideanNorm x < 2*R
    exact (div_lt_iff₀ hR).mp (hnorm x ▸ hn)
  · intro x hx
    apply b.one_of_mem_closedBall
    have hn : euclideanNorm (R⁻¹ • x) ≤ 1 := by
      rw [hnorm, div_le_one hR]
      exact hx.le
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, J,
      PiLp.continuousLinearEquiv_symm_apply,
      ← TimeChange.euclideanNorm_eq_norm_toLp] using hn
  · intro x
    have hd : HasFDerivAt χ (R⁻¹ • fderiv ℝ φ (R⁻¹ • x)) x := by
      have hh := (hφ.differentiable (by simp) (R⁻¹ • x)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).const_smul R⁻¹)
      convert hh using 1
      ext v
      simp
    have hj (j : Fin d) : |gradient χ x j| ≤ N/R := by
      have hv : ‖unitVector j‖ ≤ 1 :=
        (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun k => by
          simp only [unitVector,Pi.single_apply,Real.norm_eq_abs]
          split_ifs <;> norm_num)
      change ‖fderiv ℝ χ x (unitVector j)‖ ≤ _
      rw [hd.fderiv]
      calc
        _ ≤ ‖R⁻¹ • fderiv ℝ φ (R⁻¹ • x)‖ * ‖unitVector j‖ :=
          ContinuousLinearMap.le_opNorm _ _
        _ ≤ (R⁻¹*N)*1 := by
          apply mul_le_mul _ hv (norm_nonneg _)
          · positivity
          · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hR)]
            exact mul_le_mul_of_nonneg_left (hN _) (inv_nonneg.mpr hR.le)
        _ = N/R := by ring
    calc
      euclideanSq (gradient χ x) ≤ ∑ _j : Fin d, (N/R)^2 := by
        unfold euclideanSq dot
        apply Finset.sum_le_sum
        intro j _
        have h := pow_le_pow_left₀ (abs_nonneg _) (hj j) 2
        rw [sq_abs] at h
        simpa only [pow_two] using h
      _ = (Real.sqrt (d : ℝ)*N/R)^2 := by
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        simp only [div_pow,mul_pow,Real.sq_sqrt (Nat.cast_nonneg d)]
        ring

end EinsteinRelation.Correctors
