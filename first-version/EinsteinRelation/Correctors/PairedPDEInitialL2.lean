import EinsteinRelation.Correctors.PairedPDETraceConstruction
import Mathlib.MeasureTheory.Function.LpSpace.Complete

/-! # Quadratic convergence and the strong initial trace

Source: `paper/main.tex:821–838,850`. For bounded scalar initial data the
Green-function route reduces strong local convergence to convergence of
quadratic integrals. These lemmas convert that estimate to the actual L²
classes without assuming the Cauchy property.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation.Correctors

/-- A vanishing quadratic error implies strong convergence of the actual
L² classes. Source: `paper/main.tex:821–838`. -/
theorem paired_tendsto_L2_of_quadratic {X T : Type*} [MeasurableSpace X]
    {μ : Measure X} {l : Filter T} (f : T → Lp ℝ 2 μ) (a : Lp ℝ 2 μ)
    (hlim : Tendsto (fun t => ∫ x, (f t x - a x)^2 ∂μ) l (𝓝 0)) :
    Tendsto f l (𝓝 a) := by
  have hid (t : T) : ‖f t - a‖ ^ 2 = ∫ x, (f t x - a x)^2 ∂μ := by
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_sub (f t) a] with x hx
    simp only [hx, Pi.sub_apply, RCLike.inner_apply, conj_trivial, pow_two]
  have hn : Tendsto (fun t => ‖f t - a‖ ^ 2) l (𝓝 0) := by
    simpa only [hid] using hlim
  have hs := hn.sqrt
  simp only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] at hs
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hs

/-- Quadratic convergence of pointwise representatives gives strong convergence
of their L² classes. Source: `paper/main.tex:821–838`. -/
theorem paired_tendsto_L2_of_quadratic_representatives
    {X T : Type*} [MeasurableSpace X] {μ : Measure X} {l : Filter T}
    (f : T → Lp ℝ 2 μ) {u : T → X → ℝ} {a : X → ℝ} (ha : MemLp a 2 μ)
    (hrep : ∀ᶠ t in l, (f t : X → ℝ) =ᵐ[μ] u t)
    (hlim : Tendsto (fun t => ∫ x, (u t x - a x)^2 ∂μ) l (𝓝 0)) :
    Tendsto f l (𝓝 (ha.toLp a)) := by
  apply paired_tendsto_L2_of_quadratic
  apply hlim.congr'
  filter_upwards [hrep] with t ht
  apply integral_congr_ae
  filter_upwards [ht, ha.coeFn_toLp] with x hx hax
  rw [hx, hax]

end EinsteinRelation.Correctors
