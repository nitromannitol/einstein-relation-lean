import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Large-scale thresholds for the dyadic block recursion: for `L` large the smoothing
scale `L ^ η` exceeds twice the dependence range, the doubled scale `(2L) ^ η` stays below
`L ^ β`, and the strip width `L ^ β` beats the localization diameter plus the range. -/

open Filter Topology

namespace EinsteinFull.Calculus.S1

theorem recursion_thresholds {r₀ δ η β : ℝ} (hr₀ : 1 ≤ r₀) (hδ : 0 < δ) (hη : 0 < η)
    (hβη : η < β) (hβ : η * (1 + δ) < β) :
    ∃ L₁ : ℝ, 1 ≤ L₁ ∧ ∀ L : ℝ, L₁ ≤ L →
      2 * r₀ ≤ L ^ η ∧ (2 * L) ^ η ≤ L ^ β ∧
      r₀ < L - (L - L ^ β) - 2 * (r₀ * (L ^ η / r₀) ^ (1 + δ)) := by
  have hβpos : 0 < β := by linarith
  have hε₀ : 0 < β - η * (1 + δ) := by linarith
  have hβη' : 0 < β - η := by linarith
  have e1 : ∀ᶠ L : ℝ in atTop, 2 * r₀ ≤ L ^ η :=
    (tendsto_rpow_atTop hη).eventually_ge_atTop _
  have e2a : ∀ᶠ L : ℝ in atTop, (2 : ℝ) ^ η ≤ L ^ (β - η) :=
    (tendsto_rpow_atTop hβη').eventually_ge_atTop _
  have e3a : ∀ᶠ L : ℝ in atTop, (4 : ℝ) ≤ L ^ (β - η * (1 + δ)) :=
    (tendsto_rpow_atTop hε₀).eventually_ge_atTop _
  have e3b : ∀ᶠ L : ℝ in atTop, 2 * r₀ + 1 ≤ L ^ β :=
    (tendsto_rpow_atTop hβpos).eventually_ge_atTop _
  have e0 : ∀ᶠ L : ℝ in atTop, 1 ≤ L := eventually_ge_atTop 1
  obtain ⟨L₁, hL₁⟩ := eventually_atTop.1 (e0.and (e1.and (e2a.and (e3a.and e3b))))
  refine ⟨max L₁ 1, le_max_right _ _, fun L hL => ?_⟩
  obtain ⟨h0, h1, h2a, h3a, h3b⟩ := hL₁ L (le_trans (le_max_left _ _) hL)
  have hL0 : 0 ≤ L := by linarith
  have hLpos : 0 < L := by linarith
  refine ⟨h1, ?_, ?_⟩
  · have hLβ : L ^ β = L ^ (β - η) * L ^ η := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    rw [Real.mul_rpow (by norm_num) hL0, hLβ]
    exact mul_le_mul_of_nonneg_right h2a (Real.rpow_nonneg hL0 _)
  · have hX : L ^ β = L ^ (η * (1 + δ)) * L ^ (β - η * (1 + δ)) := by
      rw [← Real.rpow_add hLpos]
      congr 1
      ring
    have hr0pos : 0 < r₀ := by linarith
    have hXnn : 0 ≤ L ^ (η * (1 + δ)) := Real.rpow_nonneg hL0 _
    have hρ : r₀ * (L ^ η / r₀) ^ (1 + δ) ≤ L ^ (η * (1 + δ)) := by
      rw [Real.div_rpow (Real.rpow_nonneg hL0 _) hr0pos.le, ← Real.rpow_mul hL0]
      have hself : r₀ ≤ r₀ ^ (1 + δ) := Real.self_le_rpow_of_one_le hr₀ (by linarith)
      rw [mul_div_assoc', div_le_iff₀ (Real.rpow_pos_of_pos hr0pos _)]
      calc r₀ * L ^ (η * (1 + δ)) = L ^ (η * (1 + δ)) * r₀ := mul_comm _ _
        _ ≤ L ^ (η * (1 + δ)) * r₀ ^ (1 + δ) := mul_le_mul_of_nonneg_left hself hXnn
    have hsmall : L ^ (η * (1 + δ)) * 4 ≤ L ^ β := by
      rw [hX]
      exact mul_le_mul_of_nonneg_left h3a hXnn
    linarith

theorem two_rpow_sq_mul_pow (d : ℕ) :
    ((2 : ℝ) ^ (-(d : ℝ) / 2)) ^ 2 * (2 : ℝ) ^ d = 1 := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ (-(d : ℝ) / 2)) 2, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_natCast (2 : ℝ) d, ← Real.rpow_add (by norm_num)]
  have : -(d : ℝ) / 2 * ((2 : ℕ) : ℝ) + (d : ℝ) = 0 := by push_cast; ring
  rw [this, Real.rpow_zero]

end EinsteinFull.Calculus.S1
