import EinsteinRelation.Correctors.PairedPDETimeTranslation
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.Deriv.Slope

/-! # Temporal cutoff difference quotients

Source: `paper/main.tex:832–840`. Compact support controls all difference
quotients uniformly, as required by the strong L² multiplier limit.
-/

namespace EinsteinRelation.Correctors

/-- Uniform scalar difference-quotient bound used for temporal energy
regularization. Source: `paper/main.tex:832–840`. -/
theorem paired_compact_time_slope_bound {η : ℝ → ℝ}
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hηc : HasCompactSupport η) :
    ∃ B : ℝ, 0 ≤ B ∧ (∀ t, ‖deriv η t‖ ≤ B) ∧
      ∀ t h : ℝ, ‖(η (t + h) - η t) / h‖ ≤ B := by
  have h1 : (1 : WithTop ℕ∞) ≤ (⊤ : ℕ∞) := by
    exact_mod_cast (le_top : (1 : ℕ∞) ≤ ⊤)
  obtain ⟨B, hB⟩ := (hη.continuous_deriv h1).bounded_above_of_compact_support hηc.deriv
  have hB0 : 0 ≤ B := (norm_nonneg (deriv η 0)).trans (hB 0)
  refine ⟨B, hB0, hB, ?_⟩
  intro t h
  by_cases hh : h = 0
  · simpa only [hh, add_zero, sub_self, zero_div, norm_zero] using hB0
  have hs : ‖η (t + h) - η t‖ ≤ B * ‖h‖ := by
    simpa only [add_sub_cancel_left] using
      Convex.norm_image_sub_le_of_norm_deriv_le
        (fun x (_ : x ∈ (Set.univ : Set ℝ)) => hη.differentiable h1 x)
        (fun x _ => hB x) convex_univ (Set.mem_univ t) (Set.mem_univ (t + h))
  rw [norm_div]
  exact (div_le_iff₀ (norm_pos_iff.mpr hh)).mpr hs

end EinsteinRelation.Correctors
