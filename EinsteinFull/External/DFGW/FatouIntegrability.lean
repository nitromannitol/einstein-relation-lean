import EinsteinFull.External.DFGW.VelocityResolvent
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-! # Integrability from bounded approximating integrals

Fatou's lemma gives integrability of a nonnegative limit when the approximating integrals are
uniformly bounded.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- A nonnegative almost-everywhere limit has finite integral if the approximating integrals
are uniformly bounded. -/
theorem integrable_of_nonneg_tendsto_integral_bounded
    {f : α → ℝ} {g : ℕ → α → ℝ} (hf : AEStronglyMeasurable f μ)
    (hfn : 0 ≤ᵐ[μ] f) (hg : ∀ n, Integrable (g n) μ) (hgn : ∀ n, 0 ≤ᵐ[μ] g n)
    (hlim : ∀ᵐ x ∂μ, Tendsto (fun n => g n x) atTop (𝓝 (f x)))
    (C : ℝ) (hbound : ∀ n, ∫ x, g n x ∂μ ≤ C) : Integrable f μ := by
  refine ⟨hf, (hasFiniteIntegral_iff_ofReal hfn).2 ?_⟩
  have hlim' : ∀ᵐ x ∂μ,
      Filter.liminf (fun n => ENNReal.ofReal (g n x)) atTop = ENNReal.ofReal (f x) := by
    filter_upwards [hlim] with x hx
    exact ((ENNReal.continuous_ofReal.tendsto _).comp hx).liminf_eq
  have hfatou := lintegral_liminf_le' (μ := μ) (u := atTop)
    (f := fun n x => ENNReal.ofReal (g n x))
    (fun n => (hg n).aemeasurable.ennreal_ofReal)
  have hle : (∫⁻ x, ENNReal.ofReal (f x) ∂μ) ≤ ENNReal.ofReal C := by
    calc
      _ = ∫⁻ x, Filter.liminf (fun n => ENNReal.ofReal (g n x)) atTop ∂μ :=
        lintegral_congr_ae (by filter_upwards [hlim'] with x hx; exact hx.symm)
      _ ≤ Filter.liminf (fun n => ∫⁻ x, ENNReal.ofReal (g n x) ∂μ) atTop := hfatou
      _ ≤ ENNReal.ofReal C := by
        apply Filter.liminf_le_of_frequently_le
        exact Filter.Eventually.frequently (Filter.Eventually.of_forall fun n => by
          rw [← ofReal_integral_eq_lintegral_ofReal (hg n) (hgn n)]
          exact ENNReal.ofReal_le_ofReal (hbound n))
        exact ⟨0, Filter.Eventually.of_forall fun _ => zero_le⟩
  exact lt_of_le_of_lt hle ENNReal.ofReal_lt_top

end EinsteinFull.External.DFGW
