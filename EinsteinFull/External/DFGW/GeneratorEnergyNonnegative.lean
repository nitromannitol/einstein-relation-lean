import EinsteinFull.External.DFGW.GeneratorEnergy

/-! # Positivity of generator energy

The generator of a contraction semigroup has nonnegative negative quadratic form.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The negative generator quadratic form is nonnegative. -/
theorem generator_energy_nonneg (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (F : (transitionSemigroup hP).generatorDomain) :
    0 ≤ -inner ℝ (F : Lp ℝ 2 μ) ((transitionSemigroup hP).generator F) := by
  apply ge_of_tendsto (tendsto_generator_energy hP F F.property)
  filter_upwards with n
  apply mul_nonneg (Nat.cast_nonneg n)
  have hnorm := (transitionOperator hP ((n : ℝ≥0)⁻¹)).le_opNorm (F : Lp ℝ 2 μ)
  have hop := norm_transitionOperator_le_one hP ((n : ℝ≥0)⁻¹)
  have hnorm' : ‖transitionOperator hP ((n : ℝ≥0)⁻¹) F‖ ≤ ‖(F : Lp ℝ 2 μ)‖ := by
    calc
      _ ≤ ‖transitionOperator hP ((n : ℝ≥0)⁻¹)‖ * ‖(F : Lp ℝ 2 μ)‖ := hnorm
      _ ≤ 1 * ‖(F : Lp ℝ 2 μ)‖ := mul_le_mul_of_nonneg_right hop (norm_nonneg _)
      _ = _ := one_mul _
  have hi := real_inner_le_norm (F : Lp ℝ 2 μ) (transitionOperator hP ((n : ℝ≥0)⁻¹) F)
  have hm := mul_le_mul_of_nonneg_left hnorm' (norm_nonneg (F : Lp ℝ 2 μ))
  nlinarith

end EinsteinFull.External.DFGW
