import EinsteinFull.Regeneration.ExponentialTailMoment
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Contraction of exponential moments on an event

Convexity makes a small exponential tilt close to one uniformly under a
bounded larger exponential moment.
-/

open MeasureTheory EinsteinRelation
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A small tilt on an event is bounded by its mass plus a fraction of a larger moment. -/
theorem exponential_moment_indicator_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] (E : Set Ω) (hE : MeasurableSet E) (X : Ω → ℝ)
    (hX : Measurable X) (b θ M : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (hlarge : Integrable (fun ω => Real.exp (b * X ω)) μ)
    (hM : (∫ ω, Real.exp (b * X ω) ∂μ) ≤ M) :
    Integrable (E.indicator (fun ω => Real.exp ((θ * b) * X ω))) μ ∧
      (∫ ω, E.indicator (fun ω => Real.exp ((θ * b) * X ω)) ω ∂μ) ≤
        μ.real E + θ * M := by
  let F : Ω → ℝ := E.indicator (fun ω => Real.exp ((θ * b) * X ω))
  let G : Ω → ℝ := fun ω => E.indicator (fun _ => (1 : ℝ)) ω + θ * Real.exp (b * X ω)
  have hF : Measurable F :=
    (Real.measurable_exp.comp (measurable_const.mul hX)).indicator hE
  have hG : Integrable G μ := ((integrable_const (1 : ℝ)).indicator hE).add (hlarge.const_mul θ)
  have hpoint : ∀ ω, 0 ≤ F ω ∧ F ω ≤ G ω := by
    intro ω
    by_cases hω : ω ∈ E
    · have hc := convexOn_exp.2 (Set.mem_univ (0 : ℝ)) (Set.mem_univ (b * X ω))
        (sub_nonneg.mpr hθ1) hθ (by ring : 1 - θ + θ = (1 : ℝ))
      have he : Real.exp ((θ * b) * X ω) ≤ 1 + θ * Real.exp (b * X ω) := by
        have he' : Real.exp ((θ * b) * X ω) ≤ (1 - θ) + θ * Real.exp (b * X ω) := by
          simpa only [smul_eq_mul, mul_zero, zero_add, Real.exp_zero, mul_one,
            mul_assoc] using hc
        linarith
      simpa only [F, G, Set.indicator_of_mem hω, Pi.one_apply] using
        ⟨(Real.exp_pos _).le, he⟩
    · simp only [F, G, Set.indicator_of_notMem hω, zero_add]
      exact ⟨le_rfl, mul_nonneg hθ (Real.exp_pos _).le⟩
  have hi : Integrable F μ := by
    apply hG.mono' hF.aestronglyMeasurable
    filter_upwards [] with ω
    rw [Real.norm_eq_abs, abs_of_nonneg (hpoint ω).1]
    exact (hpoint ω).2
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, G ω ∂μ := integral_mono_ae hi hG (Filter.Eventually.of_forall fun ω => (hpoint ω).2)
    _ = μ.real E + θ * ∫ ω, Real.exp (b * X ω) ∂μ := by
      dsimp only [G]
      rw [integral_add ((integrable_const (1 : ℝ)).indicator hE) (hlarge.const_mul θ),
        integral_const_mul]
      have he : (∫ ω, E.indicator (fun _ => (1 : ℝ)) ω ∂μ) = μ.real E := by
        change (∫ ω, E.indicator (1 : Ω → ℝ) ω ∂μ) = μ.real E
        exact integral_indicator_one hE
      rw [he]
    _ ≤ μ.real E + θ * M := by
      have h := mul_le_mul_of_nonneg_left hM hθ
      linarith

end EinsteinFull.Regeneration
