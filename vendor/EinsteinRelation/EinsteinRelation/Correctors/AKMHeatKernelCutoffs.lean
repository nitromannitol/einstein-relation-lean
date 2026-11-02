import EinsteinRelation.Calculus.Weak
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.SpecificLimits.Basic

/-! # Expanding smooth compact cutoffs

Source: `paper/main.tex:777–782,840`; cutoff removal for AKM (9.2), p. 347.
The gradient bound uses the actual coordinate norm and operator norm.
-/

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- Smooth cutoffs exhausting space have gradients bounded by C/(n+1). -/
theorem akm_exists_scaled_cutoffs (d : ℕ) :
    ∃ (χ : ℕ → Vec d → ℝ) (C : ℝ), 0 ≤ C ∧
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (χ n) ∧ HasCompactSupport (χ n)) ∧
      (∀ n x, 0 ≤ χ n x ∧ χ n x ≤ 1) ∧
      (∀ x, Tendsto (fun n => χ n x) atTop (𝓝 1)) ∧
      ∀ n x, ‖gradient (χ n) x‖ ≤ C / (n+1 : ℕ) := by
  let φ : ContDiffBump (0 : Vec d) := ⟨1, 2, by norm_num, by norm_num⟩
  have hφ : ContDiff ℝ (⊤ : ℕ∞) φ := φ.contDiff
  obtain ⟨C, hC⟩ := (φ.hasCompactSupport.fderiv ℝ).exists_bound_of_continuous
    (hφ.continuous_fderiv (by simp))
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0)
  let χ : ℕ → Vec d → ℝ := fun n x => φ (((n : ℝ)+1)⁻¹ • x)
  have hχ n : ContDiff ℝ (⊤ : ℕ∞) (χ n) := by
    have hs : ContDiff ℝ (⊤ : ℕ∞) (fun x : Vec d => (((n : ℝ)+1)⁻¹) • x) := by fun_prop
    exact φ.contDiff.comp hs
  refine ⟨χ, C, hC0, fun n => ⟨hχ n, ?_⟩,
    fun n x => ⟨φ.nonneg, φ.le_one⟩, ?_, ?_⟩
  · exact φ.hasCompactSupport.comp_smul (inv_ne_zero (by positivity))
  · intro x
    have hi : Tendsto (fun n : ℕ => ((n : ℝ)+1)⁻¹) atTop (𝓝 0) := by
      simpa only [one_div] using tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have hh : Tendsto (fun n : ℕ => φ (((n : ℝ)+1)⁻¹ • x)) atTop (𝓝 (φ ((0 : ℝ) • x))) :=
      φ.continuous.continuousAt.tendsto.comp (hi.smul_const x)
    have hzero : φ (0 : Vec d) = 1 := φ.one_of_mem_closedBall (by simp [φ])
    rw [zero_smul, hzero] at hh
    exact hh
  · intro n x
    have hn : 0 < ((n : ℝ)+1)⁻¹ := by positivity
    have hd : HasFDerivAt (χ n)
        (((n : ℝ)+1)⁻¹ • fderiv ℝ φ (((n : ℝ)+1)⁻¹ • x)) x := by
      have hh := (hφ.differentiable (by simp) (((n : ℝ)+1)⁻¹ • x)).hasFDerivAt.comp x
        ((hasFDerivAt_id x).const_smul (((n : ℝ)+1)⁻¹))
      refine hh.congr_fderiv ?_
      ext v
      simp
    apply (pi_norm_le_iff_of_nonneg (div_nonneg hC0 (by positivity))).mpr
    intro j
    change ‖fderiv ℝ (χ n) x (unitVector j)‖ ≤ _
    rw [hd.fderiv]
    calc
      _ ≤ ‖((n : ℝ)+1)⁻¹ • fderiv ℝ φ (((n : ℝ)+1)⁻¹ • x)‖ * ‖unitVector j‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖((n : ℝ)+1)⁻¹ • fderiv ℝ φ (((n : ℝ)+1)⁻¹ • x)‖ * 1 := by
        gcongr
        exact (pi_norm_le_iff_of_nonneg (by norm_num : (0 : ℝ) ≤ 1)).mpr
          (fun i => by simp [unitVector, Pi.single_apply]; split_ifs <;> norm_num)
      _ ≤ ((n : ℝ)+1)⁻¹ * C := by
        rw [mul_one, norm_smul, Real.norm_eq_abs, abs_of_pos hn]
        exact mul_le_mul_of_nonneg_left (hC _) hn.le
      _ = C / (n+1 : ℕ) := by simp [div_eq_mul_inv, mul_comm]

end EinsteinRelation.Correctors
