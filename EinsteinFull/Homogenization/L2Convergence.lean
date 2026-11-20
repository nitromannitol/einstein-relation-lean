import Homogenization.Sobolev.Foundations.DifferenceQuotient

/-!
# Square-integral and L² convergence

The Dirichlet competitor definition in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (1.7),
uses convergence of squared integrals. This is equivalent to L² convergence
when the functions are square integrable.
-/

open MeasureTheory Filter Topology

namespace EinsteinFull.Homogenization

/-- Square-integral convergence to zero and L² seminorm convergence to zero
are equivalent for square-integrable real-valued functions. -/
theorem tendsto_integral_sq_iff_eLpNorm {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : ℕ → α → ℝ} (hf : ∀ n, MemLp (f n) 2 μ) :
    Tendsto (fun n => ∫ x, (f n x) ^ 2 ∂μ) atTop (𝓝 0) ↔
      Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0) := by
  have hsq : ∀ n, ((eLpNorm (f n) 2 μ).toReal) ^ 2 =
      ∫ x, (f n x) ^ 2 ∂μ := fun n =>
    _root_.Homogenization.toReal_eLpNorm_two_sq_eq_integral_sq (hf n)
  rw [← ENNReal.tendsto_toReal_zero_iff (fun n => (hf n).eLpNorm_ne_top)]
  constructor
  · intro h
    have hs := Real.continuous_sqrt.continuousAt.tendsto.comp h
    simp only [Real.sqrt_zero] at hs
    apply hs.congr
    intro n
    change Real.sqrt (∫ x, (f n x) ^ 2 ∂μ) = _
    rw [← hsq n, Real.sqrt_sq (ENNReal.toReal_nonneg)]
  · intro h
    have hs := h.pow 2
    simp only [zero_pow (by decide : (2 : ℕ) ≠ 0)] at hs
    exact hs.congr fun n => hsq n

end EinsteinFull.Homogenization
