import EinsteinRelation.Correctors.PairedPDELinearConvergence
import EinsteinRelation.Correctors.SpaceTimeConvolutionL2
import EinsteinRelation.Correctors.PairedPDEQuadraticConvergence

/-! # Strong L² limits used by the actual energy test

Source: `paper/main.tex:832–840`. Fixed bounded cutoff factors, sums,
and restriction preserve the strong L² approximation of the weak field.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

/-- A fixed bounded cutoff preserves strong L² convergence.
Source: `paper/main.tex:832–840`. -/
theorem paired_tendsto_fixed_multiplier_L2 {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u w : X → ℝ} {us : ℕ → X → ℝ}
    (hu : MemLp u 2 μ) (hus : ∀ k, MemLp (us k) 2 μ) (hw : MemLp w ∞ μ)
    (hlim : Tendsto (fun k => eLpNorm (fun x => us k x - u x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => w x * us k x - w x * u x) 2 μ)
      atTop (𝓝 0) := by
  have hb := ENNReal.Tendsto.const_mul hlim (Or.inr hw.eLpNorm_ne_top)
  rw [mul_zero] at hb
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
    (fun _ => zero_le _) (fun k => ?_)
  simpa only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, mul_sub] using
    eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm (2 : ℝ≥0∞) ((hus k).sub hu).1 w

/-- Restriction preserves the global L² approximation.
Source: `paper/main.tex:832–840`. -/
theorem paired_tendsto_restrict_L2 {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {f : X → ℝ} {fs : ℕ → X → ℝ} (s : Set X)
    (hlim : Tendsto (fun k => eLpNorm (fun x => fs k x - f x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => eLpNorm (fun x => fs k x - f x) 2 (μ.restrict s))
      atTop (𝓝 0) :=
  tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
    (fun _ => zero_le _) (fun _ => eLpNorm_restrict_le _ _ _ _)

end EinsteinRelation.Correctors
