import EinsteinRelation.Correctors.StationaryLocalL2Square
import EinsteinRelation.Correctors.ExpectedSquareSummability

/-! Source: `paper/main.tex:722,756`. Stationary environment moment
bounds give almost sure local L² convergence of the actual spatial errors. -/
open MeasureTheory Filter Topology
open scoped ENNReal
namespace EinsteinRelation.Correctors

/-- A stationary error with environment L² norm `O(1/n)` tends to zero
almost surely in local L². Every error is genuinely locally square integrable. -/
theorem ae_local_L2_zero_of_stationary_error_bound {d : ℕ}
    (Q : Measure (FieldPair d)) [SFinite Q] (hQ : IsStationary Q)
    (ν : Measure (Vec d)) [IsFiniteMeasure ν]
    (f : ℕ → FieldPair d → ℝ) (hf : ∀ n, Measurable (f n))
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ n, eLpNorm (f n) 2 Q ≤ ENNReal.ofReal (C / ((n : ℝ) + 1))) :
    ∀ᵐ ω ∂Q,
      (∀ n, MemLp (fun x => f n (translate x ω)) 2 ν) ∧
      Tendsto (fun n => eLpNorm (fun x => f n (translate x ω)) 2 ν)
        atTop (𝓝 0) := by
  let X : ℕ → FieldPair d → ℝ≥0∞ :=
    fun n ω => eLpNorm (fun x => f n (translate x ω)) 2 ν
  have hmeas (n : ℕ) : Measurable (fun q : FieldPair d × Vec d => f n (translate q.2 q.1)) :=
    (hf n).comp (Probability.continuous_translate.measurable.comp measurable_swap)
  have hXm (n : ℕ) : Measurable (X n) := by
    have h := (ENNReal.continuous_rpow_const (y := (1 / (2 : ℝ)))).measurable.comp
      (Measurable.lintegral_prod_right' (ν := ν) ((hmeas n).enorm.pow_const (2 : ℝ)))
    convert h using 1
    funext ω
    dsimp [X]
    rw [eLpNorm_eq_lintegral_rpow_enorm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)]
    norm_num
  let M : ℝ≥0∞ := ν Set.univ * ENNReal.ofReal (C^2)
  have hM : M ≠ ∞ := ENNReal.mul_ne_top (measure_ne_top _ _) ENNReal.ofReal_ne_top
  have hEX (n : ℕ) : (∫⁻ ω, (X n ω)^2 ∂Q) ≤
      M * ENNReal.ofReal (1 / ((n : ℝ) + 1)^2) := by
    change (∫⁻ ω, (eLpNorm (fun x => f n (translate x ω)) 2 ν)^2 ∂Q) ≤ _
    rw [lintegral_stationary_local_L2_square Q hQ ν (f n) (hf n)]
    calc
      ν Set.univ * (eLpNorm (f n) 2 Q)^2 ≤
          ν Set.univ * (ENNReal.ofReal (C / ((n : ℝ) + 1)))^2 :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left' (hbound n) 2) (zero_le _)
      _ = M * ENNReal.ofReal (1 / ((n : ℝ) + 1)^2) := by
        dsimp [M]
        rw [← ENNReal.ofReal_pow (div_nonneg hC (by positivity)),
          mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg C)]
        congr 2
        simp only [div_eq_mul_inv, mul_pow, one_mul, inv_pow]
  have hfin (n : ℕ) : ∀ᵐ ω ∂Q, X n ω < ∞ := by
    have hI : (∫⁻ ω, (X n ω)^2 ∂Q) < ∞ :=
      (hEX n).trans_lt (ENNReal.mul_lt_top hM.lt_top ENNReal.ofReal_lt_top)
    filter_upwards [ae_lt_top' ((hXm n).aemeasurable.pow_const 2) hI.ne] with ω hω
    by_contra hh
    have ht : X n ω = ∞ := eq_top_iff.mpr (not_lt.mp hh)
    simp [ht] at hω
  filter_upwards [ae_all_iff.mpr hfin,
    ae_tendsto_zero_of_expected_square_quadratic_bound Q X
      (fun n => (hXm n).aemeasurable) M hM hEX] with ω hω hlim
  refine ⟨fun n => ⟨?_, hω n⟩, hlim⟩
  exact ((hf n).comp (Probability.continuous_translate.measurable.comp
    (measurable_id.prodMk measurable_const))).aestronglyMeasurable

end EinsteinRelation.Correctors
