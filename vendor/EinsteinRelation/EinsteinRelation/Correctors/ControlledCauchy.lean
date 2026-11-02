import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Topology.MetricSpace.Cauchy

/-! # Cauchy control for normalized local potentials

Source: `paper/main.tex:713–727`.
-/

open Filter Topology
namespace EinsteinRelation.Correctors

/-- A Poincaré difference bound transfers the Cauchy property to centered
potentials (`paper/main.tex:727-729`). -/
theorem cauchySeq_of_norm_sub_le {E F : Type*}
    [NormedAddCommGroup E] [NormedAddCommGroup F]
    (u : ℕ → E) (g : ℕ → F) (C : ℝ)
    (hg : CauchySeq g)
    (h : ∀ n m, ‖u n - u m‖ ≤ C * ‖g n - g m‖) : CauchySeq u := by
  by_cases hCpos : 0 < C
  · -- C > 0: use the Cauchy property of g scaled by C
    rw [Metric.cauchySeq_iff] at hg ⊢
    intro ε hε
    have hεdivC : 0 < ε / C := div_pos hε hCpos
    rcases hg (ε / C) hεdivC with ⟨N, hN⟩
    refine ⟨N, fun n hn m hm => ?_⟩
    have hgnm_dist := hN n hn m hm
    have hgnm_norm : ‖g n - g m‖ < ε / C := by
      simpa [dist_eq_norm] using hgnm_dist
    have hbound := h n m
    have hlt : C * ‖g n - g m‖ < ε := by
      calc
        C * ‖g n - g m‖ < C * (ε / C) := mul_lt_mul_of_pos_left hgnm_norm hCpos
        _ = ε := by field_simp [ne_of_gt hCpos]
    have : dist (u n) (u m) < ε := by
      simpa [dist_eq_norm] using lt_of_le_of_lt hbound hlt
    exact this
  · -- C ≤ 0: then ‖u n - u m‖ ≤ 0, so u is constant
    have hCnonpos : C ≤ 0 := by linarith
    have hconst : ∀ n m, u n = u m := by
      intro n m
      have hbound := h n m
      have hnonneg_u : 0 ≤ ‖u n - u m‖ := norm_nonneg _
      have hnonneg_g : 0 ≤ ‖g n - g m‖ := norm_nonneg _
      have : C * ‖g n - g m‖ ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hCnonpos hnonneg_g
      have hzero : ‖u n - u m‖ ≤ 0 := le_trans hbound this
      have heq : ‖u n - u m‖ = 0 := le_antisymm hzero hnonneg_u
      exact sub_eq_zero.mp (norm_eq_zero.mp heq)
    rw [Metric.cauchySeq_iff]
    intro ε hε
    refine ⟨0, fun n hn m hm => ?_⟩
    have heq : u n = u m := hconst n m
    simpa [heq] using hε

end EinsteinRelation.Correctors
