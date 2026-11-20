import EinsteinFull.Homogenization.SourceResponseTauSummability
import Mathlib.Analysis.Normed.Group.Tannery

/-!
# Geometric sums of summable sequences

Geometrically weighted sums of a nonnegative summable sequence vanish as the
upper limit increases. This applies to the response-defect sums in Lemma 2.13
of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*.
-/

open Filter Topology

namespace EinsteinFull.Homogenization

/-- Geometric averages of a nonnegative summable sequence tend to zero. -/
theorem tendsto_sum_geometric_mul_of_summable (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ < 1)
    (f : ℕ → ℝ) (hf0 : ∀ n, 0 ≤ f n) (hf : Summable f) :
    Tendsto (fun n : ℕ => ∑ m ∈ Finset.range n, θ ^ (n - 1 - m) * f m)
      atTop (𝓝 0) := by
  let F : ℕ → ℕ → ℝ := fun n m => if m < n then θ ^ (n - 1 - m) * f m else 0
  have hexp (m : ℕ) : Tendsto (fun n : ℕ => n - 1 - m) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    filter_upwards [eventually_ge_atTop (b + 1 + m)] with n hn
    omega
  have hlim (m : ℕ) : Tendsto (fun n => F n m) atTop (𝓝 0) := by
    have h := ((tendsto_pow_atTop_nhds_zero_of_lt_one hθ0 hθ1).comp (hexp m)).mul_const (f m)
    simp only [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [eventually_gt_atTop m] with n hn
    simp only [F, hn, ↓reduceIte, Function.comp_apply]
  have hbound : ∀ᶠ n : ℕ in atTop, ∀ m, ‖F n m‖ ≤ f m := by
    filter_upwards with n m
    by_cases hmn : m < n
    · simp only [F, hmn, ↓reduceIte, Real.norm_eq_abs,
        abs_of_nonneg (mul_nonneg (pow_nonneg hθ0 _) (hf0 m))]
      exact mul_le_of_le_one_left (hf0 m) (pow_le_one₀ hθ0 hθ1.le)
    · simp only [F, hmn, ↓reduceIte, norm_zero]
      exact hf0 m
  have ht := tendsto_tsum_of_dominated_convergence (g := fun _ : ℕ => (0 : ℝ)) hf hlim hbound
  simp only [tsum_zero] at ht
  refine ht.congr' (Eventually.of_forall fun n => ?_)
  rw [tsum_eq_sum (s := Finset.range n)]
  · apply Finset.sum_congr rfl
    intro m hm
    simp only [F, Finset.mem_range.mp hm, ↓reduceIte]
  · intro m hm
    simp only [Finset.mem_range, not_lt] at hm
    simp [F, not_lt.mpr hm]

end EinsteinFull.Homogenization
