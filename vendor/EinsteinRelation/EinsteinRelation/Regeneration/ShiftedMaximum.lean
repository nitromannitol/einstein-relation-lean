import EinsteinRelation.Regeneration.Construction

/-! # Running maximum under an actual time shift

Source `paper/main.tex:305–314,365–374`. Splitting the past at a finite shift
relates the literal running maximum to the shifted path's running maximum.
This supports the failed-trial restart geometry; no probabilistic assertion is used.
-/

open scoped NNReal ENNReal

namespace EinsteinRelation.Regeneration

/-- Exact finite-time splitting identity for the actual displacement maximum. -/
theorem coordinateMaximum_add {d : ℕ} (γ : Path d) (i : Fin d) (s t : ℝ≥0) :
    coordinateMaximum γ i (s + t) = max (coordinateMaximum γ i s)
      (γ s i - γ 0 i + coordinateMaximum (pathTimeShift γ s) i t) := by
  apply le_antisymm
  · apply coordinateMaximum_le
    intro u hu
    by_cases hus : u ≤ s
    · exact (displacement_le_coordinateMaximum γ i u s hus).trans (le_max_left _ _)
    · have hsu : s ≤ u := le_of_not_ge hus
      have hut : u - s ≤ t := tsub_le_iff_right.mpr (by simpa only [add_comm] using hu.2)
      have hsplit : s + (u - s) = u := add_tsub_cancel_of_le hsu
      have h := displacement_le_coordinateMaximum (pathTimeShift γ s) i (u - s) t hut
      change γ (s + (u - s)) i - γ (s + 0) i ≤
        coordinateMaximum (pathTimeShift γ s) i t at h
      rw [add_zero, hsplit] at h
      exact (by linarith : γ u i - γ 0 i ≤
        γ s i - γ 0 i + coordinateMaximum (pathTimeShift γ s) i t).trans (le_max_right _ _)
  · apply max_le
    · apply coordinateMaximum_le
      intro u hu
      exact displacement_le_coordinateMaximum γ i u (s + t)
        (hu.2.trans (le_add_of_nonneg_right zero_le))
    · have h : coordinateMaximum (pathTimeShift γ s) i t ≤
          coordinateMaximum γ i (s + t) - (γ s i - γ 0 i) := by
        apply coordinateMaximum_le
        intro u hu
        have hbound := displacement_le_coordinateMaximum γ i (s + u) (s + t)
          (add_le_add le_rfl hu.2)
        simp only [pathTimeShift, ContinuousMap.coe_mk, add_zero]
        linarith only [hbound]
      linarith only [h]

end EinsteinRelation.Regeneration
