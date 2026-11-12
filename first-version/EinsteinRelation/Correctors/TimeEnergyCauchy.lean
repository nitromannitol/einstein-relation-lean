import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Data.Real.ConjExponents
import Mathlib.Data.Real.Sqrt
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory Set

namespace EinsteinRelation.Correctors

/-- Time Cauchy--Schwarz for a Banach-valued path, paper/main.tex:844–848: the squared norm of
the Bochner time integral of `g` over `[0, T]` is at most `T` times the integrated squared norm.
This consumes the time-energy quantity produced upstream; no energy estimate is assumed. The
argument is uniform in `T ≥ 0`, so `T = 0` needs no separate case. -/
theorem norm_time_integral_sq_le_energy : ∀ {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] {T : ℝ}, 0 ≤ T →
    ∀ g : ℝ → E, MemLp g 2 (volume.restrict (Icc 0 T)) →
    ‖∫ t in Icc (0 : ℝ) T, g t‖^2 ≤ T * ∫ t in Icc (0 : ℝ) T, ‖g t‖^2 := by
  intro E _ _ _ T hT g hg
  -- Scalar Hölder with exponents (2, 2) applied to the constant `1` and `‖g‖`.
  have hp2 : ENNReal.ofReal (2 : ℝ) = 2 := ENNReal.ofReal_ofNat 2
  have hf : MemLp (fun _ : ℝ => (1 : ℝ)) (ENNReal.ofReal 2) (volume.restrict (Icc (0 : ℝ) T)) :=
    memLp_const 1
  have hgn : MemLp (fun t => ‖g t‖) (ENNReal.ofReal 2) (volume.restrict (Icc (0 : ℝ) T)) := by
    rw [hp2]
    exact hg.norm
  have H0 := integral_mul_le_Lp_mul_Lq_of_nonneg (μ := volume.restrict (Icc (0 : ℝ) T))
    (f := fun _ : ℝ => (1 : ℝ)) (g := fun t => ‖g t‖) Real.HolderConjugate.two_two
    (ae_of_all _ fun _ => zero_le_one) (ae_of_all _ fun t => norm_nonneg (g t)) hf hgn
  -- Evaluate the constant-one and power integrals on `Icc 0 T`; `∫ 1 = T` since `T ≥ 0`.
  have H : ∫ t in Icc (0 : ℝ) T, ‖g t‖
      ≤ Real.sqrt T * Real.sqrt (∫ t in Icc (0 : ℝ) T, ‖g t‖ ^ 2) := by
    -- `Real.rpow_two` makes the constant `1 ^ 2` a natural power, so `one_pow` reduces it to `1`.
    simp only [one_mul, one_pow, setIntegral_const, smul_eq_mul, mul_one,
      Real.volume_real_Icc_of_le hT, sub_zero, Real.rpow_two, ← Real.sqrt_eq_rpow] at H0
    exact H0
  have hS1 : 0 ≤ ∫ t in Icc (0 : ℝ) T, ‖g t‖ := integral_nonneg fun t => norm_nonneg (g t)
  have hS2 : 0 ≤ ∫ t in Icc (0 : ℝ) T, ‖g t‖ ^ 2 := integral_nonneg fun t => sq_nonneg _
  calc ‖∫ t in Icc (0 : ℝ) T, g t‖ ^ 2
      ≤ (∫ t in Icc (0 : ℝ) T, ‖g t‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_integral_le_integral_norm g) 2
    _ ≤ (Real.sqrt T * Real.sqrt (∫ t in Icc (0 : ℝ) T, ‖g t‖ ^ 2)) ^ 2 :=
        pow_le_pow_left₀ hS1 H 2
    _ = T * ∫ t in Icc (0 : ℝ) T, ‖g t‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hT, Real.sq_sqrt hS2]

end EinsteinRelation.Correctors
