import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Tactic

open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

/-- Choose a base in the initial dyadic interval for any later terminal scale. -/
theorem c14_dyadic_exact_terminal_scale (T₀ t : ℝ) (hT₀ : 0 < T₀) (ht : T₀ ≤ t) : ∃ N : ℕ, ∃ T : ℝ, T₀ ≤ T ∧ T < 2*T₀ ∧ t = (2 : ℝ)^N*T := by
  have hratio : 1 ≤ t / T₀ := (le_div_iff₀ hT₀).2 (by simpa using ht)
  obtain ⟨N, hlow, hhigh⟩ := exists_nat_pow_near hratio (show (1 : ℝ) < 2 by norm_num)
  have hp : 0 < (2 : ℝ) ^ N := by positivity
  refine ⟨N, t / (2 : ℝ) ^ N, ?_, ?_, ?_⟩
  · apply (le_div_iff₀ hp).2
    have := (le_div_iff₀ hT₀).1 hlow
    nlinarith
  · apply (div_lt_iff₀ hp).2
    have := (div_lt_iff₀ hT₀).1 hhigh
    rw [pow_succ] at this
    nlinarith
  · field_simp

end EinsteinFull.Blueprint
