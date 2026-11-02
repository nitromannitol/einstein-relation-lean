import EinsteinRelation.Regeneration.BoundedHorizonPastBarrier
import EinsteinRelation.Regeneration.NoBacktrackingPrefix
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory Filter Topology
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinRelation.Regeneration

/-- Source `paper/main.tex:381`: bounded convergence for the literal finite-horizon no-backtracking barriers. -/
theorem tendsto_integral_finite_barrier {d : ℕ}
    (μ : Measure (CoupledSample d)) [IsFiniteMeasure μ]
    (Δ : ℝ≥0) (hΔ : 0 < Δ) (R : ℝ) (i : Fin d)
    (F : CoupledSample d → ℝ) (hF : Measurable F) (hb : BoundedRealTest F) :
    Tendsto (fun n : ℕ => ∫ z, (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ →
      -R < z.1 t i - z.1 0 i then F z else 0) ∂μ) atTop
      (𝓝 (∫ z, (if NoBacktracking R z.1 i then F z else 0) ∂μ)) := by
  obtain ⟨C, hC⟩ := hb
  have hC_nonneg : 0 ≤ C :=
    calc
      0 ≤ |F (Classical.arbitrary _)| := abs_nonneg _
      _ ≤ C := hC _
  set f : ℕ → CoupledSample d → ℝ := fun n z =>
    if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i then F z else 0
  set fl : CoupledSample d → ℝ := fun z =>
    if NoBacktracking R z.1 i then F z else 0
  set g : CoupledSample d → ℝ := fun _ => C
  have hg_int : Integrable g μ := integrable_const _
  have h_meas : ∀ n, AEStronglyMeasurable (f n) μ := by
    intro n
    have h_set : MeasurableSet {z : CoupledSample d |
        ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i} :=
      (Probability.finiteHistorySigma_le (d := d) Δ n) _
        (measurableSet_noBacktracking_prefix Δ n R i)
    have hF_ae : AEStronglyMeasurable F μ := hF.aestronglyMeasurable
    have h_eq : f n = Set.indicator {z : CoupledSample d |
        ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i} F := by
      ext z
      rfl
    rw [h_eq]
    exact hF_ae.indicator h_set
  have h_bound : ∀ n, ∀ᵐ z ∂μ, ‖f n z‖ ≤ g z := by
    intro n
    refine ae_of_all _ fun z => ?_
    dsimp [f, g]
    split_ifs with h
    · have hcz := hC z
      simpa [Real.norm_eq_abs] using hcz
    · simpa [Real.norm_eq_abs, abs_zero] using hC_nonneg
  have h_lim : ∀ᵐ z ∂μ, Tendsto (fun n : ℕ => f n z) atTop (𝓝 (fl z)) := by
    refine ae_of_all _ fun z => ?_
    dsimp [f, fl]
    by_cases hNB : NoBacktracking R z.1 i
    · have h_all : ∀ t : ℝ≥0, -R < z.1 t i - z.1 0 i :=
        (noBacktracking_iff_forall R z.1 i).mp hNB
      have h_all' : ∀ n : ℕ, ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i := by
        intro n t _
        exact h_all t
      have h_fl_eq : (if NoBacktracking R z.1 i then F z else 0) = F z := by simp [hNB]
      have h_fn_eq : (fun (n : ℕ) => (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i then F z else 0)) = fun _ : ℕ => F z := by
        ext n
        have h := h_all' n
        split_ifs
        · rfl
      have h_flim : Tendsto (fun _ : ℕ => F z) atTop (𝓝 (F z)) := tendsto_const_nhds
      rw [h_fl_eq, h_fn_eq]
      exact h_flim
    · have h_not_all : ¬ ∀ t : ℝ≥0, -R < z.1 t i - z.1 0 i := by
        rwa [noBacktracking_iff_forall R z.1 i] at hNB
      push_neg at h_not_all
      obtain ⟨t₀, ht₀⟩ := h_not_all
      have h_eventually_false : ∀ᶠ n : ℕ in atTop,
          ¬ (∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i) := by
        let N : ℕ := Nat.ceil ((t₀ : ℝ) / (Δ : ℝ))
        have hN : (t₀ : ℝ≥0) ≤ (N : ℝ≥0) * Δ := by
          have hceil : (t₀ : ℝ) / (Δ : ℝ) ≤ (N : ℝ) :=
            mod_cast Nat.le_ceil ((t₀ : ℝ) / (Δ : ℝ))
          have hposΔ : (0 : ℝ) < Δ := by exact mod_cast hΔ
          have hineq : (t₀ : ℝ) ≤ (N : ℝ) * (Δ : ℝ) := by
            calc
              (t₀ : ℝ) = ((t₀ : ℝ) / (Δ : ℝ)) * (Δ : ℝ) := by
                field_simp [hposΔ.ne.symm]
              _ ≤ (N : ℝ) * (Δ : ℝ) := mul_le_mul_of_nonneg_right hceil (by linarith)
          exact mod_cast hineq
        refine Filter.eventually_atTop.mpr ⟨N, fun n hn => ?_⟩
        intro h
        have h_lt : -R < z.1 t₀ i - z.1 0 i :=
          h t₀ (calc
            t₀ ≤ (N : ℝ≥0) * Δ := hN
            _ ≤ (n : ℝ≥0) * Δ := mul_le_mul_of_nonneg_right (by exact_mod_cast hn) zero_le)
        linarith
      have h_fl_eq : (if NoBacktracking R z.1 i then F z else 0) = 0 := by simp [hNB]
      have h_fn_eventually : (fun _ : ℕ => (0 : ℝ)) =ᶠ[atTop]
          (fun n : ℕ => (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i then F z else 0)) := by
        filter_upwards [h_eventually_false] with n hn
        rw [if_neg hn]
      have h_zero : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 (0 : ℝ)) := tendsto_const_nhds
      have h_fn_tendsto : Tendsto (fun n : ℕ => (if ∀ t : ℝ≥0, t ≤ (n : ℝ≥0) * Δ → -R < z.1 t i - z.1 0 i then F z else 0)) atTop (𝓝 (0 : ℝ)) :=
        Filter.Tendsto.congr' h_fn_eventually h_zero
      rw [h_fl_eq]
      exact h_fn_tendsto
  exact tendsto_integral_of_dominated_convergence g h_meas hg_int h_bound h_lim

end EinsteinRelation.Regeneration
