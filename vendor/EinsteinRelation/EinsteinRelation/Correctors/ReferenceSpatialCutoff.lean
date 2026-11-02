import EinsteinRelation.Correctors.PrescribedBallCutoff
import EinsteinRelation.Sharpness.Energy

namespace EinsteinRelation.Correctors
open External.AKM
open EinsteinRelation.Sharpness

/-- A nonnegative Euclidean reference cutoff with a uniform gradient bound.
Source: `paper/main.tex:818–824`. -/
theorem exists_nonnegative_reference_spatial_cutoff (d : ℕ) :
    ∃ (χ : Vec d → ℝ) (D : ℝ), 0 < D ∧
      IsSpatialTest (originBall d 2) χ ∧
      (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      (∀ x ∈ originBall d 1, χ x = 1) ∧
      ∀ x, euclideanSq (gradient χ x) ≤ D^2 := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    ⟨1, 3/2, by norm_num, by norm_num⟩
  let χ : Vec d → ℝ := b ∘ J
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := b.contDiff.comp J.contDiff
  have hc : HasCompactSupport χ := b.hasCompactSupport.comp_homeomorph J.toHomeomorph
  obtain ⟨N, hN⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hχ.continuous_fderiv (by simp))
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  have h_nonneg : ∀ x, 0 ≤ χ x := by
    intro x
    dsimp [χ]
    exact b.nonneg (x := J x)
  have h_le_one : ∀ x, χ x ≤ 1 := by
    intro x
    dsimp [χ]
    exact b.le_one (x := J x)
  have h_one_on_ball : ∀ x ∈ originBall d 1, χ x = 1 := by
    intro x hx
    dsimp [χ]
    apply b.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, J,
      PiLp.continuousLinearEquiv_symm_apply,
      ← TimeChange.euclideanNorm_eq_norm_toLp] using
      (le_of_lt (show euclideanNorm x < 1 from hx))
  have h_spatial : IsSpatialTest (originBall d 2) χ := by
    refine ⟨hχ, hc, ?_⟩
    intro x hx
    have heq := tsupport_comp_eq_preimage (b : EuclideanSpace ℝ (Fin d) → ℝ)
      J.toHomeomorph
    rw [b.tsupport_eq] at heq
    have hx' : J x ∈ Metric.closedBall 0 (3/2) :=
      (Set.ext_iff.mp heq x).mp hx
    have hn : euclideanNorm x ≤ 3/2 := by
      simpa only [Metric.mem_closedBall, dist_eq_norm, sub_zero, J,
        PiLp.continuousLinearEquiv_symm_apply,
        ← TimeChange.euclideanNorm_eq_norm_toLp] using hx'
    change euclideanNorm x < 2
    linarith
  have h_grad_bound : ∀ x, euclideanSq (gradient χ x) ≤ (Real.sqrt (d : ℝ) * N + 1)^2 := by
    intro x
    have hj (j : Fin d) : |gradient χ x j| ≤ N := by
      have hv : ‖unitVector j‖ ≤ 1 :=
        (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun k => by
          simp only [unitVector, Pi.single_apply, Real.norm_eq_abs]
          split_ifs <;> norm_num)
      exact ((fderiv ℝ χ x).le_opNorm (unitVector j)).trans
        ((mul_le_mul (hN x) hv (norm_nonneg _) hN0).trans_eq (mul_one N))
    have h_norm : euclideanNorm (gradient χ x) ≤ Real.sqrt (d : ℝ) * N := by
      unfold euclideanNorm euclideanSq dot
      calc
        Real.sqrt (∑ j, gradient χ x j * gradient χ x j) ≤
            Real.sqrt (∑ _j : Fin d, N^2) := by
          apply Real.sqrt_le_sqrt
          exact Finset.sum_le_sum fun j _ => by
            have hh : |gradient χ x j|^2 ≤ N^2 :=
              pow_le_pow_left₀ (abs_nonneg _) (hj j) 2
            rw [sq_abs] at hh
            simpa only [pow_two] using hh
        _ = Real.sqrt (d : ℝ)*N := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          rw [Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hN0]
    have h_nonneg_sqrt : 0 ≤ Real.sqrt (d : ℝ) * N :=
      mul_nonneg (Real.sqrt_nonneg _) hN0
    have h_sq : euclideanSq (gradient χ x) ≤ (Real.sqrt (d : ℝ) * N)^2 := by
      have h_nonneg_bound : 0 ≤ Real.sqrt (d : ℝ) * N :=
        mul_nonneg (Real.sqrt_nonneg _) hN0
      rw [euclideanNorm] at h_norm
      calc
        euclideanSq (gradient χ x) = (Real.sqrt (euclideanSq (gradient χ x)))^2 := by
          rw [Real.sq_sqrt (euclideanSq_nonneg _)]
        _ ≤ (Real.sqrt (d : ℝ) * N)^2 :=
          pow_le_pow_left₀ (Real.sqrt_nonneg _) h_norm 2
    have hD : Real.sqrt (d : ℝ) * N ≤ Real.sqrt (d : ℝ) * N + 1 := by nlinarith
    nlinarith
  refine ⟨χ, Real.sqrt (d : ℝ) * N + 1, ?_, h_spatial, ?_, h_one_on_ball, h_grad_bound⟩
  · have h_nonneg_sqrt : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    nlinarith
  · intro x
    exact ⟨h_nonneg x, h_le_one x⟩

end EinsteinRelation.Correctors
