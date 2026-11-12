import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Function.LpSpace.Complete

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- A uniform bound on exhausting cutoff energies gives global energy.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof. -/
theorem memLp_two_of_cutoff_energy_bound {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {g : Ω → ℝ} (hg : AEStronglyMeasurable g μ)
    {χ : ℕ → Ω → ℝ} (hχ : ∀ᵐ x ∂μ, Tendsto (fun n => χ n x) atTop (𝓝 1))
    {C : ℝ} (hi : ∀ n, Integrable (fun x => χ n x ^ 2 * g x ^ 2) μ)
    (hC : ∀ n, (∫ x, χ n x ^ 2 * g x ^ 2 ∂μ) ≤ C) :
    MemLp g 2 μ ∧ (∫ x, g x ^ 2 ∂μ) ≤ C := by
  let f : ℕ → Ω → ℝ := fun n x => χ n x ^ 2 * g x ^ 2
  have hnonneg (n : ℕ) (x : Ω) : 0 ≤ f n x := mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hC0 : 0 ≤ C := (integral_nonneg (hnonneg 0)).trans (hC 0)
  have hlim : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x ^ 2)) := by
    filter_upwards [hχ] with x hx
    simpa only [one_pow, one_mul] using (hx.pow 2).mul_const (g x ^ 2)
  have hnorm (n : ℕ) : eLpNorm (f n) 1 μ = ENNReal.ofReal (∫ x, f n x ∂μ) := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm (hi n)]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => Real.norm_of_nonneg (hnonneg n x)
  have hle : eLpNorm (fun x => g x ^ 2) 1 μ ≤ ENNReal.ofReal C := by
    apply Lp.eLpNorm_le_of_ae_tendsto _ (fun n => (hi n).aestronglyMeasurable) hlim
    exact Filter.Eventually.of_forall fun n => by
      rw [hnorm]
      exact ENNReal.ofReal_le_ofReal (hC n)
  have hgi : Integrable (fun x => g x ^ 2) μ :=
    memLp_one_iff_integrable.mp ⟨hg.pow 2, hle.trans_lt ENNReal.ofReal_lt_top⟩
  refine ⟨(memLp_two_iff_integrable_sq hg).mpr hgi, ?_⟩
  have hnormg : ENNReal.ofReal (∫ x, g x ^ 2 ∂μ) = eLpNorm (fun x => g x ^ 2) 1 μ := by
    rw [eLpNorm_one_eq_lintegral_enorm, ← ofReal_integral_norm_eq_lintegral_enorm hgi]
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => (Real.norm_of_nonneg (sq_nonneg (g x))).symm
  exact (ENNReal.ofReal_le_ofReal_iff hC0).mp (hnormg.trans_le hle)

end EinsteinRelation.Correctors
