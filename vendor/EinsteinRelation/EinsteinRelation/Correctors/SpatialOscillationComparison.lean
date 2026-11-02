import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Probability.Moments.Variance

/-!
# Comparing centered spatial oscillations

Source: `paper/main.tex:693-698`. Centering decreases the mean square;
separating a scalar approximant costs only the elementary square inequality.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- Subtracting the average decreases the second moment of an L² function. -/
theorem average_sq_sub_average_le_average_sq {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (f : A → ℝ) (hf : MemLp f 2 μ) :
    (⨍ x, (f x - ⨍ y, f y ∂μ)^2 ∂μ) ≤ ⨍ x, f x^2 ∂μ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hmass : μ Set.univ ≠ 0 := fun h => hμ (Measure.measure_univ_eq_zero.mp h)
  let ν := (μ Set.univ)⁻¹ • μ
  letI : IsProbabilityMeasure ν := ⟨by
    simp only [ν, Measure.smul_apply, smul_eq_mul]
    exact ENNReal.inv_mul_cancel hmass (measure_ne_top μ Set.univ)⟩
  have hfn : MemLp f 2 ν := hf.smul_measure (ENNReal.inv_ne_top.mpr hmass)
  simpa only [ProbabilityTheory.variance_eq_integral hfn.aemeasurable,
    average, ν, Pi.pow_apply] using
    ProbabilityTheory.variance_le_expectation_sq hfn.aestronglyMeasurable

/-- Separate a centered approximation error from the uncentered scalar
second moment of the approximant. -/
theorem average_centered_sq_le_error_and_approximation {A : Type*} [MeasurableSpace A]
    (μ : Measure A) [IsFiniteMeasure μ] (u v : A → ℝ)
    (hu : MemLp u 2 μ) (hv : MemLp v 2 μ) :
    (⨍ x, (u x - ⨍ y, u y ∂μ)^2 ∂μ) ≤
      2 * (⨍ x, ((u x - v x) - ⨍ y, (u y - v y) ∂μ)^2 ∂μ) +
      2 * (⨍ x, v x^2 ∂μ) := by
  have hmean : (⨍ x, u x - v x ∂μ) = (⨍ x, u x ∂μ) - ⨍ x, v x ∂μ :=
    integral_sub (hu.integrable (by norm_num)).to_average
      (hv.integrable (by norm_num)).to_average
  have he : Integrable (fun x => ((u x - v x) - ⨍ y, u y - v y ∂μ)^2) μ :=
    ((hu.sub hv).sub (memLp_const (⨍ y, u y - v y ∂μ))).integrable_sq
  have hv0 : Integrable (fun x => (v x - ⨍ y, v y ∂μ)^2) μ :=
    (hv.sub (memLp_const (⨍ y, v y ∂μ))).integrable_sq
  calc
    _ ≤ (⨍ x, 2 * ((u x - v x) - ⨍ y, u y - v y ∂μ)^2 +
        2 * (v x - ⨍ y, v y ∂μ)^2 ∂μ) := by
      apply integral_mono ((hu.sub (memLp_const (⨍ y, u y ∂μ))).integrable_sq.to_average)
        ((he.const_mul 2).add (hv0.const_mul 2)).to_average
      intro x
      dsimp only [Pi.sub_apply, Pi.add_apply]
      rw [hmean]
      nlinarith only [sq_nonneg
        (((u x - v x) - ((⨍ y, u y ∂μ) - ⨍ y, v y ∂μ)) -
          (v x - ⨍ y, v y ∂μ))]
    _ = 2 * (⨍ x, ((u x - v x) - ⨍ y, u y - v y ∂μ)^2 ∂μ) +
        2 * (⨍ x, (v x - ⨍ y, v y ∂μ)^2 ∂μ) := by
      change (∫ x, 2 * _ + 2 * _ ∂(μ Set.univ)⁻¹ • μ) = _
      rw [integral_add (he.const_mul 2).to_average (hv0.const_mul 2).to_average,
        integral_const_mul, integral_const_mul]
      rfl
    _ ≤ _ := add_le_add le_rfl
      (mul_le_mul_of_nonneg_left (average_sq_sub_average_le_average_sq μ v hv)
        (by norm_num : (0 : ℝ) ≤ 2))

end EinsteinRelation.Correctors
