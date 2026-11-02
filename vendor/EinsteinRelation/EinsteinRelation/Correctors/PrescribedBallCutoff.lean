import EinsteinRelation.Correctors.ParabolicReferenceCutoff
import EinsteinRelation.Correctors.AKMHeatKernelCutoffs

/-! # Spatial cutoffs for positive-time gradient recovery

Source: `paper/main.tex:788–796`. The cutoff uses the actual Euclidean
ball, transported through the coordinate linear equivalence.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- Every positive Euclidean ball has a smooth compact cutoff in the
ball of twice its radius. Source: `paper/main.tex:788–796`. -/
theorem exists_prescribed_spatial_ball_cutoff (d : ℕ) (r : ℝ) (hr : 0 < r) :
    ∃ (χ : Vec d → ℝ) (L : ℝ), 0 ≤ L ∧
      IsSpatialTest (originBall d (2*r)) χ ∧
      (∀ x, |χ x| ≤ 1) ∧ (∀ x ∈ originBall d r, χ x = 1) ∧
      ∀ x, euclideanNorm (gradient χ x) ≤ L := by
  let J := (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).symm
  let b : ContDiffBump (0 : EuclideanSpace ℝ (Fin d)) :=
    ⟨r, 3*r/2, hr, by linarith⟩
  let χ : Vec d → ℝ := b ∘ J
  have hχ : ContDiff ℝ (⊤ : ℕ∞) χ := b.contDiff.comp J.contDiff
  have hc : HasCompactSupport χ := b.hasCompactSupport.comp_homeomorph J.toHomeomorph
  obtain ⟨N,hN⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hχ.continuous_fderiv (by simp))
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  refine ⟨χ,Real.sqrt (d : ℝ)*N,by positivity,⟨hχ,hc,?_⟩,?_,?_,?_⟩
  · intro x hx
    have heq := tsupport_comp_eq_preimage (b : EuclideanSpace ℝ (Fin d) → ℝ)
      J.toHomeomorph
    rw [b.tsupport_eq] at heq
    have hx' : J x ∈ Metric.closedBall 0 (3*r/2) :=
      (Set.ext_iff.mp heq x).mp hx
    have hn : euclideanNorm x ≤ 3*r/2 := by
      simpa only [Metric.mem_closedBall,dist_eq_norm,sub_zero,J,
        PiLp.continuousLinearEquiv_symm_apply,
        ← TimeChange.euclideanNorm_eq_norm_toLp] using hx'
    change euclideanNorm x < 2*r
    linarith
  · intro x
    change |b (J x)| ≤ 1
    exact abs_le.mpr ⟨by linarith [b.nonneg (x := J x)],b.le_one⟩
  · intro x hx
    apply b.one_of_mem_closedBall
    simpa only [Metric.mem_closedBall,dist_eq_norm,sub_zero,J,
      PiLp.continuousLinearEquiv_symm_apply,
      ← TimeChange.euclideanNorm_eq_norm_toLp] using
      (le_of_lt (show euclideanNorm x < r from hx))
  · intro x
    have hj (j : Fin d) : |gradient χ x j| ≤ N := by
      have hv : ‖unitVector j‖ ≤ 1 :=
        (pi_norm_le_iff_of_nonneg zero_le_one).mpr (fun k => by
          simp only [unitVector,Pi.single_apply,Real.norm_eq_abs]
          split_ifs <;> norm_num)
      exact ((fderiv ℝ χ x).le_opNorm (unitVector j)).trans
        ((mul_le_mul (hN x) hv (norm_nonneg _) hN0).trans_eq (mul_one N))
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
        simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
        rw [Real.sqrt_mul (Nat.cast_nonneg d),Real.sqrt_sq hN0]

end EinsteinRelation.Correctors
