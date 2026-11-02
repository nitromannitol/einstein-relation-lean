import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Tactic

/-! # Sublinear dyadic means from their successive increments

Source: `paper/main.tex:693-698,798-806`. Summing small normalized
increments shows that the ball means grow sublinearly along dyadic radii.
-/
open Filter Topology
namespace EinsteinRelation.Correctors

/-- Small increments relative to dyadic radii force sublinear dyadic means. -/
theorem tendsto_dyadic_scaled_of_small_increments (a : ℕ → ℝ)
    (h : Tendsto (fun n => (a (n+1)-a n)/(2:ℝ)^n) atTop (𝓝 0)) :
    Tendsto (fun n => a n/(2:ℝ)^n) atTop (𝓝 0) := by
  rw [Metric.tendsto_atTop] at h ⊢
  intro ε hε
  obtain ⟨N, hN⟩ := h (ε/4) (by positivity)
  have hinc (n : ℕ) (hn : N ≤ n) : |a (n+1)-a n| ≤ ε/4*(2:ℝ)^n := by
    have hi := hN n hn
    rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos (pow_pos (by norm_num : (0:ℝ)<2) n)] at hi
    exact (div_le_iff₀ (pow_pos (by norm_num : (0:ℝ)<2) n)).mp hi.le
  have hbound (n : ℕ) (hn : N ≤ n) :
      |a n| ≤ |a N| + ε/4*((2:ℝ)^n-(2:ℝ)^N) := by
    induction n, hn using Nat.le_induction with
    | base => simp
    | succ n hn ih =>
      calc
        |a (n+1)| = |a n + (a (n+1)-a n)| := by congr 1; ring
        _ ≤ |a n| + |a (n+1)-a n| := abs_add_le _ _
        _ ≤ (|a N|+ε/4*((2:ℝ)^n-(2:ℝ)^N)) + ε/4*(2:ℝ)^n :=
          add_le_add ih (hinc n hn)
        _ = |a N|+ε/4*((2:ℝ)^(n+1)-(2:ℝ)^N) := by rw [pow_succ]; ring
  have hlim : Tendsto (fun n : ℕ => |a N|/(2:ℝ)^n) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop
      (tendsto_pow_atTop_atTop_of_one_lt (by norm_num : (1:ℝ)<2))
  obtain ⟨M, hM⟩ := (Metric.tendsto_atTop.mp hlim) (ε/2) (by positivity)
  refine ⟨max N M, fun n hn => ?_⟩
  have hp : 0 < (2:ℝ)^n := pow_pos (by norm_num : (0:ℝ)<2) n
  have hb := (div_le_div_iff_of_pos_right hp).mpr (hbound n (le_trans (le_max_left _ _) hn))
  have hm := hM n (le_trans (le_max_right _ _) hn)
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (div_nonneg (abs_nonneg _) hp.le)] at hm
  rw [Real.dist_eq, sub_zero, abs_div, abs_of_pos hp]
  have hs : 0 ≤ ε/4*((2:ℝ)^N/(2:ℝ)^n) := by positivity
  have halg : (|a N|+ε/4*((2:ℝ)^n-(2:ℝ)^N))/(2:ℝ)^n =
      |a N|/(2:ℝ)^n + ε/4 - ε/4*((2:ℝ)^N/(2:ℝ)^n) := by
    field_simp
    ring
  rw [halg] at hb
  linarith

end EinsteinRelation.Correctors
