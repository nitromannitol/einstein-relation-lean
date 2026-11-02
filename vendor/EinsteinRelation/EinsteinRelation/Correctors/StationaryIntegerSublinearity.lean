import EinsteinRelation.Correctors.ScalarOrbitLocalL2
import EinsteinRelation.Correctors.StationarySpatialIntegral
import EinsteinRelation.Correctors.SummableSampleErrors
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Average
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors
/-- Scalar stationary L² orbits divided by integer radius vanish in spatial
mean square, by summability of inverse-square expected errors.
Source: `paper/main.tex:693-698`. -/
theorem ae_scalar_orbit_integer_scaled_mean_square_zero {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : Lp ℝ 2 Q) :
    ∀ᵐ ω ∂Q, Tendsto (fun n : ℕ => (((n : ℝ) + 1) ^ 2)⁻¹ *
      (⨍ x in Metric.closedBall (0 : Vec d) ((n : ℝ) + 1),
        |f (translate x ω)| ^ 2 ∂volume)) atTop (𝓝 0) := by
  let ν := fun n : ℕ => volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1))
  let F := fun ω => |f ω| ^ 2
  let H := fun (n : ℕ) ω => (((n : ℝ) + 1)^2)⁻¹ * (⨍ x, F (translate x ω) ∂ν n)
  have hm : Measurable F := (Lp.stronglyMeasurable f).measurable.norm.pow_const 2
  have hi : Integrable F Q := by
    simpa only [Real.norm_eq_abs] using
      (memLp_two_iff_integrable_sq_norm (Lp.memLp f).aestronglyMeasurable).mp (Lp.memLp f)
  have hν (n : ℕ) : 0 < (ν n).real Set.univ := by
    dsimp [ν]
    rw [Measure.real, Measure.restrict_apply_univ, Real.volume_pi_closedBall _ (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
    exact pow_pos (by positivity) _
  have hcalc (n : ℕ) : Integrable (fun ω => ∫ x, F (translate x ω) ∂ν n) Q ∧
      (∫ ω, ∫ x, F (translate x ω) ∂ν n ∂Q) =
        ((ν n) Set.univ).toReal * ∫ ω, F ω ∂Q := by
    letI : IsFiniteMeasure (ν n) := isFiniteMeasure_restrict.mpr
      (isCompact_closedBall (0 : Vec d) _).measure_ne_top
    exact (stationary_spatial_integral Q hQ (ν n) F hm hi).2
  have hH (n : ℕ) : Integrable (H n) Q := by
    simpa only [H, average_eq, smul_eq_mul] using
      ((hcalc n).1.const_mul ((ν n).real Set.univ)⁻¹).const_mul (((n : ℝ) + 1)^2)⁻¹
  have hnonneg (n : ℕ) (ω : FieldPair d) : 0 ≤ H n ω := by
    dsimp [H]
    refine mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) ?_
    have := average_eq (ν n) (fun x => F (translate x ω))
    rw [this, smul_eq_mul]
    refine mul_nonneg ?_ (integral_nonneg (fun x => sq_nonneg _))
    exact inv_nonneg.mpr (by
      have : 0 < (ν n).real Set.univ := hν n
      positivity)
  have hmean (n : ℕ) : (∫ ω, ‖H n ω‖ ∂Q) =
      (((n : ℝ) + 1)^2)⁻¹ * ∫ ω, F ω ∂Q := by
    rw [integral_congr_ae (ae_of_all _ fun ω => Real.norm_of_nonneg (hnonneg n ω))]
    dsimp only [H]
    simp_rw [average_eq, smul_eq_mul]
    rw [integral_const_mul, integral_const_mul, (hcalc n).2]
    change _ * (((ν n).real Set.univ)⁻¹ * ((ν n).real Set.univ * _)) = _
    rw [← mul_assoc (((ν n).real Set.univ)⁻¹), inv_mul_cancel₀ (hν n).ne', one_mul]
  have hs : Summable (fun n : ℕ => (((n : ℝ) + 1)^2)⁻¹) := by
    simpa only [Nat.cast_add, Nat.cast_one, one_div] using
      (summable_nat_add_iff 1).mpr (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < 2))
  apply ae_tendsto_zero_of_summable_integral_norm Q H hH
  simpa only [hmean] using hs.mul_right (∫ ω, F ω ∂Q)
end EinsteinRelation.Correctors
