import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Measure.Regular

/-!
# Absolute continuity from an `L²` domination on bounded continuous tests

Abstract step (SI-8, `si8-domination-1`). If a finite Borel measure `μ` on a pseudo-metrizable
space satisfies `∫ f dμ ≤ C * (∫ f² dν)^{1/2}` for every nonnegative bounded continuous `f`
(`ν` finite), then `μ A ≤ C * ν A ^ {1/2}` for every Borel set `A`, hence `μ ≪ ν`. The proof uses
the outer approximation of closed sets by bounded continuous functions and inner regularity by
closed sets.
-/

open MeasureTheory Filter BoundedContinuousFunction
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull

variable {Ω : Type*} [TopologicalSpace Ω] [TopologicalSpace.PseudoMetrizableSpace Ω]
  [MeasurableSpace Ω] [BorelSpace Ω]

/-- The `L²` domination on bounded continuous tests passes to closed sets. -/
theorem measure_isClosed_le_of_lintegral_le_sqrt (μ ν : Measure Ω) [IsFiniteMeasure ν]
    (C : ℝ≥0∞) (hC : C ≠ ∞)
    (h : ∀ f : Ω →ᵇ ℝ≥0, ∫⁻ x, (f x : ℝ≥0∞) ∂μ ≤
      C * (∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ))
    {F : Set Ω} (hF : IsClosed F) :
    μ F ≤ C * ν F ^ (1 / 2 : ℝ) := by
  have hlimν := HasOuterApproxClosed.tendsto_lintegral_apprSeq hF ν
  have hlim : Tendsto (fun n => C * (∫⁻ x, (hF.apprSeq n x : ℝ≥0∞) ∂ν) ^ (1 / 2 : ℝ))
      atTop (𝓝 (C * ν F ^ (1 / 2 : ℝ))) := by
    refine ENNReal.Tendsto.const_mul ?_ (Or.inr hC)
    exact (ENNReal.continuous_rpow_const.tendsto _).comp hlimν
  refine ge_of_tendsto hlim (Eventually.of_forall fun n => ?_)
  refine (HasOuterApproxClosed.measure_le_lintegral hF μ n).trans ((h _).trans ?_)
  refine mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (lintegral_mono fun x => ?_) (by norm_num))
  have h1 : (hF.apprSeq n x : ℝ≥0∞) ≤ 1 := by
    exact_mod_cast HasOuterApproxClosed.apprSeq_apply_le_one hF n x
  calc (hF.apprSeq n x : ℝ≥0∞) ^ 2 = (hF.apprSeq n x : ℝ≥0∞) * (hF.apprSeq n x : ℝ≥0∞) := sq _
    _ ≤ (hF.apprSeq n x : ℝ≥0∞) * 1 := mul_le_mul' le_rfl h1
    _ = (hF.apprSeq n x : ℝ≥0∞) := mul_one _

/-- The `L²` domination on bounded continuous tests passes to all Borel sets. -/
theorem measure_le_of_lintegral_le_sqrt (μ ν : Measure Ω) [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] (C : ℝ≥0∞) (hC : C ≠ ∞)
    (h : ∀ f : Ω →ᵇ ℝ≥0, ∫⁻ x, (f x : ℝ≥0∞) ∂μ ≤
      C * (∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ))
    {A : Set Ω} (hA : MeasurableSet A) :
    μ A ≤ C * ν A ^ (1 / 2 : ℝ) := by
  rw [hA.measure_eq_iSup_isClosed_of_ne_top (measure_ne_top μ A)]
  refine iSup₂_le fun K hK => iSup_le fun hKc => ?_
  refine (measure_isClosed_le_of_lintegral_le_sqrt μ ν C hC h hKc).trans ?_
  exact mul_le_mul' le_rfl (ENNReal.rpow_le_rpow (measure_mono hK) (by norm_num))

/-- `L²` domination on bounded continuous tests gives absolute continuity. -/
theorem absolutelyContinuous_of_lintegral_le_sqrt (μ ν : Measure Ω) [IsFiniteMeasure ν]
    [IsFiniteMeasure μ] (C : ℝ≥0∞) (hC : C ≠ ∞)
    (h : ∀ f : Ω →ᵇ ℝ≥0, ∫⁻ x, (f x : ℝ≥0∞) ∂μ ≤
      C * (∫⁻ x, (f x : ℝ≥0∞) ^ 2 ∂ν) ^ (1 / 2 : ℝ)) :
    μ ≪ ν := by
  refine Measure.AbsolutelyContinuous.mk fun A hA hν => ?_
  have := measure_le_of_lintegral_le_sqrt μ ν C hC h hA
  rw [hν, ENNReal.zero_rpow_of_pos (by norm_num), mul_zero] at this
  exact nonpos_iff_eq_zero.mp this

end EinsteinFull
