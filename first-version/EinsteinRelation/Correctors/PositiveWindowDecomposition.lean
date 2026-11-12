import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! Source: `paper/main.tex:722,756`. Decomposition of genuine positive
time integrals into the interior window and its two endpoint windows. -/
open MeasureTheory
namespace EinsteinRelation.Correctors

/-- The two short endpoint windows account for the exact difference
between nested finite time windows. -/
theorem integral_Icc_remove_endpoint_windows
    (f : ℝ → ℝ) (a s t b : ℝ) (has : a ≤ s) (hst : s ≤ t) (htb : t ≤ b)
    (hf : IntegrableOn f (Set.Icc a b)) :
    (∫ u in Set.Icc s t, f u) =
      (∫ u in Set.Icc a b, f u) -
        (∫ u in Set.Icc a s, f u) - (∫ u in Set.Icc t b, f u) := by
  have hi (x y : ℝ) (hax : a ≤ x) (hxy : x ≤ y) (hyb : y ≤ b) :
      IntervalIntegrable f volume x y := by
    apply (intervalIntegrable_iff_integrableOn_Icc_of_le hxy).mpr
    exact hf.mono_set (fun z hz => ⟨hax.trans hz.1, hz.2.trans hyb⟩)
  have h₁ := intervalIntegral.integral_add_adjacent_intervals
    (hi a s le_rfl has (hst.trans htb)) (hi s t has hst htb)
  have h₂ := intervalIntegral.integral_add_adjacent_intervals
    (hi a t le_rfl (has.trans hst) htb) (hi t b (has.trans hst) htb le_rfl)
  have hset (x y : ℝ) (hxy : x ≤ y) :
      (∫ u in Set.Icc x y, f u) = ∫ u in x..y, f u := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hxy]
  rw [hset s t hst, hset a b (has.trans (hst.trans htb)), hset a s has, hset t b htb]
  linarith

end EinsteinRelation.Correctors
