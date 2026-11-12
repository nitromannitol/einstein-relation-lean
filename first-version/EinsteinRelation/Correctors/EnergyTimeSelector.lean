import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.Deriv.Support

namespace EinsteinRelation.Correctors

open Set
open Metric

/-- Auxiliary temporal localization for the polarized energy identity;
source `paper/main.tex:824–832`. Construct a reference test equal to one
near the support of the prescribed temporal test. -/
theorem exists_energy_time_selector {a b : ℝ} {η : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η)
    (hηs : tsupport η ⊆ Set.Ioo a b) :
    ∃ ρ : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      tsupport ρ ⊆ Set.Ioo a b ∧
      (∀ t, η t * ρ t = η t) ∧
      (∀ t, η t * deriv ρ t = 0) ∧
      (∀ t, ρ t * deriv η t = deriv η t) := by
  classical
  rcases (tsupport η).eq_empty_or_nonempty with hempty | hne
  · have he : η = fun _ => 0 := by
      funext t
      by_contra ht
      have := subset_tsupport η ht
      simp [hempty] at this
    subst η
    exact ⟨fun _ => 0, contDiff_const, (by simp [HasCompactSupport]), by simp,
      by simp, by simp, by simp⟩
  let c := (a + b) / 2
  let R := (b - a) / 2
  have hdist {t : ℝ} (ht : t ∈ Set.Ioo a b) : dist t c < R := by
    rw [Real.dist_eq, abs_lt]
    dsimp [c, R]
    constructor <;> linarith [ht.1, ht.2]
  obtain ⟨t, ht, hmax⟩ := hηc.exists_isMaxOn hne
    (continuous_id.dist (continuous_const : Continuous (fun _ : ℝ => c))).continuousOn
  have htR : dist t c < R := hdist (hηs ht)
  let r := (dist t c + R) / 2
  have hr : 0 < r := by dsimp [r]; linarith [dist_nonneg (x := t) (y := c)]
  let ρ : ContDiffBump c :=
    { rIn := r
      rOut := (r + R) / 2
      rIn_pos := hr
      rIn_lt_rOut := by dsimp [r]; linarith }
  have hnear {x : ℝ} (hx : x ∈ tsupport η) :
      (ρ : ℝ → ℝ) =ᶠ[nhds x] fun _ => 1 := by
    apply ρ.eventuallyEq_one_of_mem_ball
    change dist x c < r
    have hle : dist x c ≤ dist t c := hmax hx
    dsimp [r]
    linarith
  have hs : tsupport (ρ : ℝ → ℝ) ⊆ Set.Ioo a b := by
    rw [ρ.tsupport_eq]
    intro x hx
    have hrad : (r + R) / 2 < R := by dsimp [r]; linarith only [htR]
    have hle : dist x c < R := lt_of_le_of_lt hx hrad
    rw [Real.dist_eq, abs_lt] at hle
    dsimp only [c, R] at hle
    constructor <;> linarith only [hle.1, hle.2]
  refine ⟨ρ, ρ.contDiff, ρ.hasCompactSupport, hs, ?_, ?_, ?_⟩
  · intro x
    by_cases hx : η x = 0
    · simp [hx]
    · rw [(hnear (subset_tsupport η hx)).eq_of_nhds, mul_one]
  · intro x
    by_cases hx : η x = 0
    · simp [hx]
    · have hd : deriv (ρ : ℝ → ℝ) x = 0 :=
        (hnear (subset_tsupport η hx)).deriv_eq.trans (deriv_const x 1)
      rw [hd, mul_zero]
  · intro x
    by_cases hx : deriv η x = 0
    · simp [hx]
    · rw [(hnear (support_deriv_subset hx)).eq_of_nhds, one_mul]
end EinsteinRelation.Correctors
