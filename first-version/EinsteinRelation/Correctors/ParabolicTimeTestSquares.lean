import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.FDeriv.Add
import Mathlib.Topology.MetricSpace.ProperSpace.Lemmas

open scoped Topology
namespace EinsteinRelation.Correctors

/-- Compact time tests are differences of squares with the same open support.
Source: `paper/main.tex:787–792,850`; weak forward/backward duality. -/
theorem compact_time_test_difference_squares {a b : ℝ} {η : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b) :
    ∃ ρ σ : ℝ → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧ tsupport ρ ⊆ Set.Ioo a b ∧
      ContDiff ℝ (⊤ : ℕ∞) σ ∧ HasCompactSupport σ ∧ tsupport σ ⊆ Set.Ioo a b ∧
      ∀ t, η t = ρ t ^ 2 - σ t ^ 2 ∧
        deriv η t = 2 * ρ t * deriv ρ t - 2 * σ t * deriv σ t := by
  by_cases hab : a < b
  · let c := (a+b)/2
    let R := (b-a)/2
    have hR : 0 < R := by dsimp [R]; linarith
    have hs : tsupport η ⊆ Metric.ball c R := by
      intro t ht
      have hh := hηs ht
      rw [Metric.mem_ball, Real.dist_eq, abs_lt]
      dsimp [c, R]
      constructor <;> linarith [hh.1, hh.2]
    obtain ⟨r, ⟨hr, hrR⟩, hsr⟩ := exists_pos_lt_subset_ball hR (isClosed_tsupport η) hs
    let θ : ContDiffBump c :=
      ⟨r, (r+R)/2, hr, by linarith⟩
    have hθs : tsupport (θ : ℝ → ℝ) ⊆ Set.Ioo a b := by
      rw [θ.tsupport_eq]
      intro t ht
      rw [Metric.mem_closedBall, Real.dist_eq, abs_le] at ht
      dsimp [θ, c, R] at ht
      dsimp [R] at hrR
      constructor <;> linarith [ht.1, ht.2]
    have hθone (t : ℝ) (ht : η t ≠ 0) : θ t = 1 :=
      θ.one_of_mem_closedBall (Metric.ball_subset_closedBall (hsr (subset_tsupport η ht)))
    let ρ : ℝ → ℝ := fun t => (θ t+η t)/2
    let σ : ℝ → ℝ := fun t => (θ t-η t)/2
    have hρ : ContDiff ℝ (⊤ : ℕ∞) ρ := (θ.contDiff.add hη).div_const 2
    have hσ : ContDiff ℝ (⊤ : ℕ∞) σ := (θ.contDiff.sub hη).div_const 2
    have hρc : HasCompactSupport ρ := (θ.hasCompactSupport.add hηc).mono (by
        intro t ht
        exact (div_ne_zero_iff.mp ht).1)
    have hσc : HasCompactSupport σ := (θ.hasCompactSupport.sub hηc).mono (by
        intro t ht
        exact (div_ne_zero_iff.mp ht).1)
    have hρs : tsupport ρ ⊆ Set.Ioo a b := by
      apply (closure_mono (show Function.support ρ ⊆ Function.support
        (fun t => θ t + η t) from fun t ht => (div_ne_zero_iff.mp ht).1)).trans
      exact (tsupport_add _ _).trans (Set.union_subset hθs hηs)
    have hσs : tsupport σ ⊆ Set.Ioo a b := by
      apply (closure_mono (show Function.support σ ⊆ Function.support
        (fun t => θ t - η t) from fun t ht => (div_ne_zero_iff.mp ht).1)).trans
      exact (tsupport_sub _ _).trans (Set.union_subset hθs hηs)
    have heq (t : ℝ) : η t = ρ t^2-σ t^2 := by
      dsimp [ρ, σ]
      by_cases ht : η t = 0
      · rw [ht]; ring
      · rw [hθone t ht]; ring
    refine ⟨ρ, σ, hρ, hρc, hρs, hσ, hσc, hσs, fun t => ⟨heq t, ?_⟩⟩
    have hh := congrArg (fun f : ℝ → ℝ => deriv f t) (funext heq)
    change deriv η t = deriv (fun x => ρ x ^ 2 - σ x ^ 2) t at hh
    have hd := ((hρ.differentiable (by simp) t).hasDerivAt.pow 2).sub
      ((hσ.differentiable (by simp) t).hasDerivAt.pow 2)
    have hf : ρ^2-σ^2 = (fun x => ρ x^2-σ x^2) := by ext x; simp
    have hhD := hd.deriv
    rw [hf] at hhD
    exact hh.trans (by simpa using hhD)

  · have hη0 : η = 0 := by
      funext t
      by_contra ht
      have hh := hηs (subset_tsupport η ht)
      exact hab (hh.1.trans hh.2)
    subst η
    refine ⟨0, 0, contDiff_const, HasCompactSupport.zero, ?_, contDiff_const,
      HasCompactSupport.zero, ?_, ?_⟩ <;> simp

end EinsteinRelation.Correctors
