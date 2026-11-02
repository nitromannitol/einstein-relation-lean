import EinsteinRelation.Correctors.BilinearLimitIntegrals
import EinsteinRelation.Correctors.PairedPDEWeakTesting
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Quadratic limits in regularized energy tests

Source: `paper/main.tex:822–830`. Strong L² convergence controls pairings
of two independently varying factors. The result applies to regularized
solutions and gradients without requiring convergence of time derivatives.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

/-- Bounded measurable weights preserve convergence of quadratic energies.
Source: `paper/main.tex:822–830`. -/
theorem paired_tendsto_integral_weighted_sq_L2 {X : Type*} [MeasurableSpace X]
    {μ : Measure X} {u w : X → ℝ} {useq : ℕ → X → ℝ}
    (hu : MemLp u 2 μ) (hus : ∀ k, MemLp (useq k) 2 μ)
    (hw : AEStronglyMeasurable w μ) {B : ℝ} (hB : ∀ᵐ x ∂μ, ‖w x‖ ≤ B)
    (hulim : Tendsto (fun k => eLpNorm (fun x => useq k x - u x) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun k => ∫ x, w x * (useq k x)^2 ∂μ) atTop
      (𝓝 (∫ x, w x * (u x)^2 ∂μ)) := by
  have hwm : MemLp w ∞ μ := memLp_top_of_bound hw B hB
  have hwu : MemLp (fun x => w x * u x) 2 μ := hwm.fun_mul hu
  have hwus (k : ℕ) : MemLp (fun x => w x * useq k x) 2 μ := hwm.fun_mul (hus k)
  have hlim : Tendsto (fun k => eLpNorm
      (fun x => w x * useq k x - w x * u x) 2 μ) atTop (𝓝 0) := by
    have hb := ENNReal.Tendsto.const_mul hulim (Or.inr hwm.eLpNorm_ne_top)
    rw [mul_zero] at hb
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hb
      (fun _ => zero_le) (fun k => ?_)
    simpa only [Pi.smul_apply, smul_eq_mul, Pi.sub_apply, mul_sub] using!
      eLpNorm_smul_le_eLpNorm_top_mul_eLpNorm (f := useq k - u) (2 : ℝ≥0∞) hw
  have h := paired_tendsto_integral_mul_L2 hu hwu hus hwus hulim hlim
  simpa only [pow_two, mul_left_comm, mul_comm, mul_assoc] using h

end EinsteinRelation.Correctors
