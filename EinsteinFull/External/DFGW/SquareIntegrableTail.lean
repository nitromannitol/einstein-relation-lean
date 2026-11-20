import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Tails of square-integrable variables

Square integrability forces the tail probability at scale `√n` to be `o(1/n)`.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- A square-integrable real variable has `n P[f² ≥ δn] → 0` for every positive `δ`. -/
theorem tendsto_nat_mul_measureReal_sq_tail_zero (f : Ω → ℝ) (hf : StronglyMeasurable f)
    (hf2 : MemLp f 2 P) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => (n : ℝ) * P.real {ω | δ * n ≤ f ω ^ 2}) atTop (𝓝 0) := by
  let S : ℕ → Set Ω := fun n => {ω | δ * n ≤ f ω ^ 2}
  let F : ℕ → Ω → ℝ := fun n => (S n).indicator (fun ω => f ω ^ 2)
  have hS (n : ℕ) : MeasurableSet (S n) := measurableSet_le measurable_const (hf.measurable.pow_const 2)
  have hF (n : ℕ) : AEStronglyMeasurable (F n) P :=
    (hf.pow 2).indicator (hS n) |>.aestronglyMeasurable
  have hdom (n : ℕ) : ∀ᵐ ω ∂P, ‖F n ω‖ ≤ ‖f ω ^ 2‖ := by
    filter_upwards with ω
    by_cases hω : ω ∈ S n <;> simp [F, hω, sq_nonneg]
  have hpoint (ω : Ω) : Tendsto (fun n => F n ω) atTop (𝓝 0) := by
    apply tendsto_const_nhds.congr'
    have h := (tendsto_natCast_atTop_atTop.atTop_mul_const hδ).eventually_gt_atTop (f ω ^ 2)
    filter_upwards [h] with n hn
    have hnot : ω ∉ S n := by change ¬ δ * (n : ℝ) ≤ f ω ^ 2; linarith
    simp [F, hnot]
  have htail : Tendsto (fun n => ∫ ω, F n ω ∂P) atTop (𝓝 0) := by
    have h := tendsto_integral_filter_of_dominated_convergence (fun ω => ‖f ω ^ 2‖)
      (Filter.Eventually.of_forall hF) (Filter.Eventually.of_forall hdom) hf2.integrable_sq.norm
      (ae_of_all P hpoint)
    simpa only [integral_zero] using h
  have hupper : Tendsto (fun n => (∫ ω, F n ω ∂P) / δ) atTop (𝓝 0) := by
    simpa only [zero_div] using htail.div_const δ
  apply squeeze_zero (g := fun n => (∫ ω, F n ω ∂P) / δ)
  · intro n
    exact mul_nonneg (Nat.cast_nonneg _) measureReal_nonneg
  · intro n
    have hconst : Integrable (fun _ : Ω => δ * (n : ℝ)) (P.restrict (S n)) := integrable_const _
    have hi : Integrable (fun ω => f ω ^ 2) (P.restrict (S n)) := hf2.integrable_sq.restrict
    have hle : (fun _ : Ω => δ * (n : ℝ)) ≤ᵐ[P.restrict (S n)] fun ω => f ω ^ 2 := by
      filter_upwards [ae_restrict_mem (hS n)] with ω hω
      exact hω
    have hbound := integral_mono_ae hconst hi hle
    rw [setIntegral_const] at hbound
    simp only [smul_eq_mul] at hbound
    have hind : (∫ ω, F n ω ∂P) = ∫ ω in S n, f ω ^ 2 ∂P :=
      integral_indicator (hS n)
    rw [hind]
    apply (le_div_iff₀ hδ).2
    change ((n : ℝ) * P.real (S n)) * δ ≤ _
    nlinarith
  · exact hupper

end EinsteinFull.External.DFGW
