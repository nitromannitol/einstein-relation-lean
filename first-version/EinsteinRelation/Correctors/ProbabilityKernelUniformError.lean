import EinsteinRelation.Correctors.PairedPDEKernelBound
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- Uniformly vanishing bounded errors have vanishing averages against
varying probability densities. Source: `paper/main.tex:787–792,850`. -/
theorem akm_probability_kernel_uniform_error
    {S Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {l : Filter S}
    {p e : S → Ω → ℝ}
    (hp : ∀ᶠ t in l, Integrable (p t) μ ∧
      (∀ᵐ x ∂μ, 0 ≤ p t x) ∧ (∫ x, p t x ∂μ) = 1)
    (he : ∀ᶠ t in l, AEStronglyMeasurable (e t) μ)
    (hlim : ∀ ε : ℝ, 0 < ε → ∀ᶠ t in l, ∀ x, |e t x| < ε) :
    Tendsto (fun t => ∫ x, p t x * e t x ∂μ) l (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  filter_upwards [hp, he, hlim (ε/2) (half_pos hε)] with t hpt het hbound
  have hb : ∀ᵐ x ∂μ, ‖e t x‖ ≤ ε/2 :=
    Filter.Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using (hbound x).le
  have hint := hpt.1.mul_bdd het hb
  calc
    dist (∫ x, p t x * e t x ∂μ) 0 = |∫ x, p t x * e t x ∂μ| := by
      rw [Real.dist_eq, sub_zero]
    _ ≤ ∫ x, |p t x * e t x| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, p t x * (ε/2) ∂μ := by
      apply integral_mono_ae hint.abs (hpt.1.mul_const (ε/2))
      filter_upwards [hpt.2.1] with x hx
      rw [abs_mul, abs_of_nonneg hx]
      exact mul_le_mul_of_nonneg_left (hbound x).le hx
    _ = ε/2 := by rw [integral_mul_const, hpt.2.2, one_mul]
    _ < ε := half_lt_self hε

end EinsteinRelation.Correctors
