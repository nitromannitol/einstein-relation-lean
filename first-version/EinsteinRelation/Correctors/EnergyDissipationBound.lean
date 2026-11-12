import EinsteinRelation.Correctors.WeakTimeFundamentalTheorem
import Mathlib.Analysis.Normed.Group.Bounded

/-! # Uniform dissipation bounds at a continuous initial trace

Source: `paper/main.tex:824–840`. A continuous energy is bounded at zero.
Integrating its genuine positive-time primitive bounds the dissipation
uniformly as the lower endpoint tends to zero. Integrability of the
energy derivative through zero is not assumed.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors

/-- Positive-time energy identities and coercivity give uniform truncated
dissipation bounds. Source: `paper/main.tex:824–840`. -/
theorem energy_dissipation_integrals_bounded
    {f g E H : ℝ → ℝ} {T : ℝ} (hT : 0 < T)
    (hf : ContinuousOn f (Set.Icc 0 T))
    (hH : IntegrableOn H (Set.Icc 0 T))
    (hHn : ∀ t ∈ Set.Icc 0 T, 0 ≤ H t)
    (hg : ∀ a : ℝ, 0 < a → a < T → IntegrableOn g (Set.Ioo a T))
    (hE : ∀ a : ℝ, 0 < a → a < T → IntegrableOn E (Set.Ioo a T))
    (hprim : ∀ a : ℝ, 0 < a → a < T →
      (∫ t in a..T, g t) = f T - f a)
    (hine : ∀ a : ℝ, 0 < a → a < T →
      ∀ᵐ t ∂volume.restrict (Set.Ioo a T), g t + E t ≤ H t) :
    ∃ C : ℝ, ∀ a : ℝ, 0 < a → a < T → (∫ t in Set.Ioo a T, E t) ≤ C := by
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn hf
  refine ⟨B - f T + ∫ t in (0 : ℝ)..T, H t, ?_⟩
  intro a ha hat
  have hgi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hat.le).mpr (hg a ha hat)
  have hEi := (intervalIntegrable_iff_integrableOn_Ioo_of_le hat.le).mpr (hE a ha hat)
  have hHi := (intervalIntegrable_iff_integrableOn_Icc_of_le hT.le).mpr hH
  have hHi' : IntervalIntegrable H volume a T := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hat.le).mpr
    exact hH.mono_set (Set.Icc_subset_Icc ha.le le_rfl)
  have hle := intervalIntegral.integral_mono_ae_restrict hat.le (hgi.add hEi) hHi' (by
    rw [← restrict_Ioo_eq_restrict_Icc]
    exact hine a ha hat)
  rw [intervalIntegral.integral_add hgi hEi, hprim a ha hat] at hle
  have hHbound : (∫ t in a..T, H t) ≤ ∫ t in (0 : ℝ)..T, H t :=
    intervalIntegral.integral_mono_interval ha.le hat.le le_rfl (by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      exact hHn t ⟨ht.1.le, ht.2⟩) hHi
  have hfa : f a ≤ B := (le_abs_self _).trans (hB a ⟨ha.le, hat.le⟩)
  rw [intervalIntegral.integral_of_le hat.le, integral_Ioc_eq_integral_Ioo] at hle
  linarith only [hle, hHbound, hfa]

end EinsteinRelation.Correctors
