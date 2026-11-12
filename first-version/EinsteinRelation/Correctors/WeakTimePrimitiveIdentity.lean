import EinsteinRelation.Correctors.WeakTimeFundamentalTheorem
import Mathlib.Analysis.Calculus.Deriv.Support

/-! # The primitive at every time from the weak time equation

Source: `paper/main.tex:832–848`. The continuous trace fixes the primitive
at every time, including the endpoints, from the distributional equation.
-/

open MeasureTheory Set
namespace EinsteinRelation.Correctors

/-- The weak time equation on an interval identifies the actual continuous
energy with its integral primitive at every time. Source:
`paper/main.tex:832–848`. -/
theorem sub_eq_intervalIntegral_of_weak_time_derivative
    {a b : ℝ} (f g : ℝ → ℝ)
    (hf : ContinuousOn f (Icc a b)) (hg : IntegrableOn g (Icc a b))
    (hweak : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo a b →
      (∫ s in Ioo a b, f s * deriv η s) = -(∫ s in Ioo a b, g s * η s)) :
    ∀ t ∈ Icc a b, f t - f a = ∫ s in a..t, g s := by
  intro t ht
  rcases eq_or_lt_of_le ht.1 with rfl | hat
  · simp
  have hsub : Icc a t ⊆ Icc a b := Icc_subset_Icc le_rfl ht.2
  have hsubo : Ioo a t ⊆ Ioo a b := Ioo_subset_Ioo le_rfl ht.2
  have hlocal : ∀ η : ℝ → ℝ, ContDiff ℝ (⊤ : ℕ∞) η → HasCompactSupport η →
      tsupport η ⊆ Ioo a t →
      (∫ s in Ioo a t, f s * deriv η s) = -(∫ s in Ioo a t, g s * η s) := by
    intro η hη hηc hηs
    have heq (v w : ℝ → ℝ) (hw : Function.support w ⊆ Ioo a t) :
        (∫ s in Ioo a b, v s * w s) = ∫ s in Ioo a t, v s * w s := by
      apply setIntegral_eq_of_subset_of_forall_diff_eq_zero measurableSet_Ioo hsubo
      intro s hs
      have hz : w s = 0 := Function.notMem_support.mp (fun h => hs.2 (hw h))
      rw [hz, mul_zero]
    have hηsupport : Function.support η ⊆ Ioo a t := (subset_tsupport η).trans hηs
    have hdsupport : Function.support (deriv η) ⊆ Ioo a t :=
      support_deriv_subset.trans hηs
    have hw := hweak η hη hηc (hηs.trans hsubo)
    rwa [heq f (deriv η) hdsupport, heq g η hηsupport] at hw
  have he := integral_eq_sub_of_weak_time_derivative hat f g (hf.mono hsub)
    (hg.mono_set hsub) hlocal
  rw [integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hat.le] at he
  exact he.symm

end EinsteinRelation.Correctors
