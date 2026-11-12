import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Smooth interval primitives. Source: `paper/main.tex:808–816,833–848`. -/
open MeasureTheory Filter Topology
namespace EinsteinRelation.Correctors

theorem intervalPrimitive_contDiff {η : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (a : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun t => ∫ s in a..t, η s) := by
  have hcont : Continuous η := hη.continuous
  have hderiv : deriv (fun t => ∫ s in a..t, η s) = η := by
    funext t
    exact (hcont.integral_hasStrictDerivAt a t).hasDerivAt.deriv
  rw [contDiff_infty_iff_deriv]
  refine ⟨fun t => (hcont.integral_hasStrictDerivAt a t).hasDerivAt.differentiableAt, ?_⟩
  rw [hderiv]
  exact hη

theorem deriv_intervalPrimitive {η : ℝ → ℝ}
    (hη : Continuous η) (a t : ℝ) :
    deriv (fun t => ∫ s in a..t, η s) t = η t := by
  exact (hη.integral_hasStrictDerivAt a t).hasDerivAt.deriv

end EinsteinRelation.Correctors
