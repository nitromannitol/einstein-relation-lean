import EinsteinRelation.Correctors.ParabolicReferenceCutoff
import Mathlib.Topology.Algebra.ConstMulAction

namespace EinsteinRelation.Correctors
open External.AKM

/-- A smooth cutoff with fixed positive time margins and Euclidean spatial
margins, for the bounded-time endpoint estimate.
Source: `paper/main.tex:798–806`. -/
theorem exists_prescribed_rectangular_cutoff (d : ℕ) (K : ℝ) :
    ∃ (ζ : ℝ × Vec d → ℝ) (M : ℝ), 0 < M ∧
      ContDiff ℝ (⊤ : ℕ∞) ζ ∧ HasCompactSupport ζ ∧
      tsupport ζ ⊆ Set.Ioo (1/2 : ℝ) (5/4) ×ˢ originBall d 4 ∧
      (∀ z, 0 ≤ ζ z ∧ ζ z ≤ 1) ∧
      (∀ z ∈ Set.Icc (3/4 : ℝ) 1 ×ˢ originBall d 2, ζ z = 1) ∧
      ∀ z, 2*ζ z*fderiv ℝ ζ z (1,0) +
        4*K^2*euclideanSq (fun j => fderiv ℝ ζ z (0,unitVector j)) ≤ M := by
  obtain ⟨φ,N₀,hN₀,hφ,hφc,hφs,hφ01,hφ1,hφD⟩ := exists_parabolic_reference_cutoff d
  let H : (ℝ × Vec d) ≃ₜ (ℝ × Vec d) :=
    ((Homeomorph.smulOfNeZero (4 : ℝ) (by norm_num)).prodCongr
      (Homeomorph.smulOfNeZero (1/2 : ℝ) (by norm_num))).trans
        (Homeomorph.addRight (-1,0))
  have hH (z : ℝ × Vec d) : H z = (4*z.1-1,(1/2 : ℝ) • z.2) := by
    rcases z with ⟨t,x⟩
    simp [H,sub_eq_add_neg,smul_eq_mul]
  let ζ : ℝ × Vec d → ℝ := φ ∘ H
  have hζ : ContDiff ℝ (⊤ : ℕ∞) ζ := by
    change ContDiff ℝ (⊤ : ℕ∞) (φ ∘ H)
    have hh : ContDiff ℝ (⊤ : ℕ∞) (H : (ℝ × Vec d) → ℝ × Vec d) := by
      simp_rw [show (H : (ℝ × Vec d) → ℝ × Vec d) =
        (fun z => (4*z.1-1,(1/2 : ℝ) • z.2)) by funext z; exact hH z]
      fun_prop
    exact hφ.comp hh
  have hc : HasCompactSupport ζ := hφc.comp_homeomorph H
  obtain ⟨N,hN⟩ := (hc.fderiv ℝ).exists_bound_of_continuous
    (hζ.continuous_fderiv (by simp))
  have hN0 : 0 ≤ N := (norm_nonneg _).trans (hN 0)
  have h01 (z) : 0 ≤ ζ z ∧ ζ z ≤ 1 := hφ01 (H z)
  refine ⟨ζ,2*N+4*K^2*(d : ℝ)*N^2+1,by positivity,hζ,hc,?_,h01,?_,?_⟩
  · intro z hz
    have hs := hφs ((Set.ext_iff.mp (tsupport_comp_eq_preimage φ H) z).mp hz)
    rw [hH] at hs
    have hx : euclideanNorm ((1/2 : ℝ) • z.2) < 2 := hs.2
    rw [TimeChange.euclideanNorm_smul,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)] at hx
    exact ⟨⟨by linarith [hs.1.1],by linarith [hs.1.2]⟩,by change euclideanNorm z.2 < 4; linarith⟩
  · intro z hz
    apply hφ1
    rw [hH]
    refine ⟨⟨by linarith [hz.1.1],by linarith [hz.1.2]⟩,?_⟩
    change euclideanNorm ((1/2 : ℝ) • z.2) < 1
    rw [TimeChange.euclideanNorm_smul,abs_of_pos (by norm_num : (0 : ℝ) < 1/2)]
    have hx : euclideanNorm z.2 < 2 := hz.2
    linarith
  · intro z
    have ht : |fderiv ℝ ζ z (1,0)| ≤ N := by
      simpa only [Prod.norm_def,norm_one,norm_zero,max_eq_left zero_le_one,mul_one,
        Real.norm_eq_abs] using ((fderiv ℝ ζ z).le_opNorm (1,0)).trans
          (mul_le_mul_of_nonneg_right (hN z) (norm_nonneg _))
    have hx (j : Fin d) : |fderiv ℝ ζ z (0,unitVector j)| ≤ N := by
      have hv : ‖((0 : ℝ),unitVector j)‖ ≤ (1 : ℝ) := by
        simp only [Prod.norm_def,norm_zero]
        apply max_le zero_le_one
        apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
        intro k
        simp only [unitVector,Pi.single_apply,Real.norm_eq_abs]
        split_ifs <;> norm_num
      exact ((fderiv ℝ ζ z).le_opNorm (0,unitVector j)).trans
        ((mul_le_mul (hN z) hv (norm_nonneg _) hN0).trans_eq (mul_one N))
    have hs : euclideanSq (fun j => fderiv ℝ ζ z (0,unitVector j)) ≤ (d : ℝ)*N^2 := by
      unfold euclideanSq dot
      calc
        _ ≤ ∑ _j : Fin d,N^2 := Finset.sum_le_sum fun j _ => by
          have hh : |fderiv ℝ ζ z (0,unitVector j)|^2 ≤ N^2 :=
            pow_le_pow_left₀ (abs_nonneg _) (hx j) 2
          rw [sq_abs] at hh
          simpa only [pow_two] using hh
        _ = _ := by simp
    have htime : 2*ζ z*fderiv ℝ ζ z (1,0) ≤ 2*N := by
      calc
        _ ≤ 2*ζ z*|fderiv ℝ ζ z (1,0)| :=
          mul_le_mul_of_nonneg_left (le_abs_self _) (mul_nonneg zero_le_two (h01 z).1)
        _ ≤ (2*1)*N := mul_le_mul
          (mul_le_mul_of_nonneg_left (h01 z).2 zero_le_two) ht (abs_nonneg _) (by norm_num)
        _ = _ := by ring
    nlinarith only [htime,mul_le_mul_of_nonneg_left hs (show 0 ≤ 4*K^2 by positivity)]

end EinsteinRelation.Correctors
