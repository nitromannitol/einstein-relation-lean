import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Support

namespace EinsteinRelation.Correctors

/-- A compact positive-time cutoff equals one on a prescribed positive strip.
Source: `paper/main.tex:787–792,850`; AKM Proposition E.1 proof. -/
theorem exists_positive_time_plateau {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ∃ (η : ℝ → ℝ) (M : ℝ),
      ContDiff ℝ (⊤ : ℕ∞) η ∧ HasCompactSupport η ∧
      tsupport η ⊆ Set.Ioo (a/2) (b+a/2) ∧
      (∀ t, 0 ≤ η t ∧ η t ≤ 1) ∧ (∀ t ∈ Set.Icc a b, η t = 1) ∧
      0 ≤ M ∧ ∀ t, |deriv η t| ≤ M := by
  set c : ℝ := (a + b) / 2 with hc
  set rIn : ℝ := (b - a) / 2 with hrIn
  set rOut : ℝ := (2 * b - a) / 4 with hrOut
  have hrIn_pos : 0 < rIn := by
    rw [hrIn]
    linarith
  have hrIn_lt_rOut : rIn < rOut := by
    rw [hrIn, hrOut]
    linarith
  let f : ContDiffBump (c : ℝ) := ⟨rIn, rOut, hrIn_pos, hrIn_lt_rOut⟩
  have h_contDiff : ContDiff ℝ (⊤ : ℕ∞) (f : ℝ → ℝ) := f.contDiff
  have h_hasCompactSupport : HasCompactSupport (f : ℝ → ℝ) := f.hasCompactSupport
  have h_tsupport : tsupport (f : ℝ → ℝ) ⊆ Set.Ioo (a/2) (b + a/2) := by
    rw [f.tsupport_eq]
    intro x hx
    rw [Metric.mem_closedBall, Real.dist_eq] at hx
    have h_abs := abs_le.mp hx
    have hx_left : a / 2 < x := by
      have h_low : c - rOut = 3 * a / 4 := by
        dsimp [c, rOut]
        ring
      have h_c_low : c - rOut ≤ x := by linarith
      have : a / 2 < 3 * a / 4 := by
        nlinarith
      linarith
    have hx_right : x < b + a / 2 := by
      have h_high : c + rOut = b + a / 4 := by
        dsimp [c, rOut]
        ring
      have h_c_high : x ≤ c + rOut := by linarith
      have : b + a / 4 < b + a / 2 := by
        nlinarith
      linarith
    exact Set.mem_Ioo.mpr ⟨hx_left, hx_right⟩
  have h_bound : ∀ t, 0 ≤ (f : ℝ → ℝ) t ∧ (f : ℝ → ℝ) t ≤ 1 := by
    intro t
    exact ⟨f.nonneg, f.le_one⟩
  have h_eq_one : ∀ t ∈ Set.Icc a b, (f : ℝ → ℝ) t = 1 := by
    intro t ht
    apply f.one_of_mem_closedBall
    rw [Metric.mem_closedBall, Real.dist_eq]
    rcases ht with ⟨ht_left, ht_right⟩
    have h_dist : |t - c| ≤ rIn := by
      rw [abs_le]
      constructor
      · dsimp [c, rIn]
        nlinarith
      · dsimp [c, rIn]
        nlinarith
    exact h_dist
  have h_deriv_bound : ∃ M : ℝ, 0 ≤ M ∧ ∀ t, |deriv (f : ℝ → ℝ) t| ≤ M := by
    have h_cont_deriv : Continuous (deriv (f : ℝ → ℝ)) :=
      f.contDiff.continuous_deriv_one
    have h_comp_supp_deriv : HasCompactSupport (deriv (f : ℝ → ℝ)) :=
      HasCompactSupport.deriv h_hasCompactSupport
    obtain ⟨C, hC⟩ := h_cont_deriv.bounded_above_of_compact_support h_comp_supp_deriv
    have h_nonneg_C : 0 ≤ C := by
      have h0 : ‖deriv (f : ℝ → ℝ) 0‖ ≤ C := hC 0
      have h0_abs : 0 ≤ |deriv (f : ℝ → ℝ) 0| := abs_nonneg _
      -- In ℝ, ‖x‖ = |x|
      simpa [Real.norm_eq_abs] using le_trans h0_abs h0
    refine ⟨C, h_nonneg_C, ?_⟩
    intro t
    -- hC gives ‖deriv f t‖ ≤ C, and we need |deriv f t| ≤ C
    -- In ℝ, ‖x‖ = |x|
    simpa [Real.norm_eq_abs] using hC t
  exact ⟨f, h_deriv_bound.choose, h_contDiff, h_hasCompactSupport, h_tsupport,
    h_bound, h_eq_one, h_deriv_bound.choose_spec.1, h_deriv_bound.choose_spec.2⟩

end EinsteinRelation.Correctors
