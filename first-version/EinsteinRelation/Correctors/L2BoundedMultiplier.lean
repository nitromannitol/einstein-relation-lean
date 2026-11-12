import Mathlib.MeasureTheory.Function.L2Space

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- Bounded almost-everywhere measurable multiplication acts continuously on L².
Source: `paper/main.tex:798–806`; the coefficient energy form uses actual
locally integrable coefficients, without a pointwise Borel assumption. -/
theorem exists_L2_bounded_multiplier_map {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (m : Ω → ℝ) (hm : AEStronglyMeasurable m μ)
    {C : ℝ} (hC : 0 ≤ C) (hb : ∀ᵐ ω ∂μ, |m ω| ≤ C) :
    ∃ T : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ, ‖T‖ ≤ C ∧
      ∀ f, (T f : Ω → ℝ) =ᵐ[μ] fun ω => m ω * f ω := by
  have h_mem (f : Lp ℝ 2 μ) : MemLp (fun ω => m ω * f ω) 2 μ :=
    (Lp.memLp f).of_le_mul
      (hm.mul (Lp.aestronglyMeasurable f))
      (by
        filter_upwards [hb] with ω hω
        simp_rw [Real.norm_eq_abs, abs_mul]
        exact mul_le_mul_of_nonneg_right hω (abs_nonneg _))
  let T_lin : Lp ℝ 2 μ →ₗ[ℝ] Lp ℝ 2 μ :=
    { toFun := fun f => (h_mem f).toLp (fun ω => m ω * f ω)
      map_add' := fun f g => by
        apply Lp.ext
        have h1 := MemLp.coeFn_toLp (h_mem (f + g))
        have h2 := MemLp.coeFn_toLp (h_mem f)
        have h3 := MemLp.coeFn_toLp (h_mem g)
        have h_add := Lp.coeFn_add ((h_mem f).toLp (fun ω => m ω * f ω))
                                     ((h_mem g).toLp (fun ω => m ω * g ω))
        have h_pointwise : (fun ω => m ω * (f + g) ω) =ᵐ[μ]
            (fun ω => m ω * f ω) + (fun ω => m ω * g ω) := by
          filter_upwards [Lp.coeFn_add f g] with ω hω
          rw [hω]
          simp [Pi.add_apply, mul_add]
        exact h1.trans (h_pointwise.trans ((h2.add h3).symm.trans h_add.symm))
      map_smul' := fun r f => by
        apply Lp.ext
        have h1 := MemLp.coeFn_toLp (h_mem (r • f))
        have h2 := MemLp.coeFn_toLp (h_mem f)
        have h_smul := Lp.coeFn_smul r ((h_mem f).toLp (fun ω => m ω * f ω))
        have h_pointwise : (fun ω => m ω * (r • f) ω) =ᵐ[μ]
            r • (fun ω => m ω * f ω) := by
          filter_upwards [Lp.coeFn_smul r f] with ω hω
          rw [hω]
          simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]
        exact h1.trans (h_pointwise.trans ((h2.const_smul r).symm.trans h_smul.symm)) }
  have h_bound : ∀ f : Lp ℝ 2 μ, ‖T_lin f‖ ≤ C * ‖f‖ := by
    intro f
    have hT_eq : T_lin f = (h_mem f).toLp (fun ω => m ω * f ω) := rfl
    rw [hT_eq]
    rw [Lp.norm_toLp]
    have h_enorm : eLpNorm (fun ω => m ω * f ω) 2 μ ≤ ENNReal.ofReal C * eLpNorm f 2 μ :=
      eLpNorm_le_mul_eLpNorm_of_ae_le_mul
        (by
          filter_upwards [hb] with ω hω
          simp_rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul_of_nonneg_right hω (abs_nonneg _))
        2
    have h_fin1 : eLpNorm (fun ω => m ω * f ω) 2 μ ≠ ∞ :=
      (h_mem f).2.ne
    have h_fin2 : eLpNorm f 2 μ ≠ ∞ :=
      (Lp.memLp f).2.ne
    calc
      ENNReal.toReal (eLpNorm (fun ω => m ω * f ω) 2 μ) ≤
          ENNReal.toReal (ENNReal.ofReal C * eLpNorm f 2 μ) :=
        ((ENNReal.toReal_le_toReal h_fin1 (by finiteness)).mpr h_enorm)
      _ = ENNReal.toReal (ENNReal.ofReal C) * ENNReal.toReal (eLpNorm f 2 μ) := by
        rw [ENNReal.toReal_mul]
      _ = C * ENNReal.toReal (eLpNorm f 2 μ) := by
        rw [ENNReal.toReal_ofReal hC]
      _ = C * ‖f‖ := by rw [Lp.norm_def]
  refine ⟨LinearMap.mkContinuous T_lin C h_bound, ?_, ?_⟩
  · -- The operator norm bound follows from `h_bound`.
    exact LinearMap.mkContinuous_norm_le _ hC h_bound
  · -- The almost-everywhere equality.
    intro f
    have hT_eq : (LinearMap.mkContinuous T_lin C h_bound) f = (h_mem f).toLp (fun ω => m ω * f ω) := rfl
    rw [hT_eq]
    simp [MemLp.coeFn_toLp (h_mem f)]

end EinsteinRelation.Correctors
