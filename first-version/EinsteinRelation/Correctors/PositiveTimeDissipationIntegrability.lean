import EinsteinRelation.Correctors.WeakTimeFundamentalTheorem
import Mathlib.MeasureTheory.Integral.SetToL1
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Integral.IntegralEqImproper

open MeasureTheory
open Set
open Filter
open scoped Topology

namespace EinsteinRelation.Correctors

/-- A bounded family of positive-time dissipation integrals is integrable
through zero. Source: `paper/main.tex:824–840`. -/
theorem integrableOn_of_positive_dissipation_integrals_bounded
    {E : ℝ → ℝ} {T C : ℝ} (hT : 0 < T)
    (hn : ∀ᵐ t ∂volume.restrict (Set.Ioo 0 T), 0 ≤ E t)
    (hi : ∀ a : ℝ, 0 < a → a < T → IntegrableOn E (Set.Ioo a T))
    (hb : ∀ a : ℝ, 0 < a → a < T → (∫ t in Set.Ioo a T, E t) ≤ C) :
    IntegrableOn E (Set.Ioo 0 T) := by
  -- Define a sequence a_n = T / (n+2) → 0+, with 0 < a_n < T for all n
  let a : ℕ → ℝ := fun n => T / ((n : ℝ) + 2)
  have ha_pos : ∀ n, 0 < a n := by
    intro n
    refine div_pos hT (by positivity)
  have ha_lt_T : ∀ n, a n < T := by
    intro n
    have h : (1 : ℝ) < (n : ℝ) + 2 := by
      have : (0 : ℕ) ≤ n := Nat.zero_le _
      have h' : (1 : ℕ) < n + 2 := by omega
      exact_mod_cast h'
    exact (div_lt_self hT h).trans_le (by norm_num)
  have ha_tendsto : Tendsto a atTop (𝓝 (0 : ℝ)) := by
    have h := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
    have h_shift : Tendsto (fun n : ℕ => (1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      h.comp (tendsto_add_atTop_nat 1)
    have h_mul : Tendsto (fun n : ℕ => T * ((1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1))) atTop (𝓝 (T * 0)) :=
      Tendsto.const_mul T h_shift
    have : (fun n : ℕ => T * ((1 : ℝ) / (((n + 1 : ℕ) : ℝ) + 1))) = a := by
      ext n
      dsimp [a]
      push_cast
      ring
    rw [this, mul_zero] at h_mul
    exact h_mul
  have hT_tendsto : Tendsto (fun _ : ℕ => T) atTop (𝓝 T) := tendsto_const_nhds
  -- AECover of Ioo 0 T by Ioo (a n) T
  have h_cover : AECover (volume.restrict (Ioo (0 : ℝ) T)) atTop (fun n => Ioo (a n) T) :=
    aecover_Ioo_of_Ioo ha_tendsto hT_tendsto
  -- For each n, E is integrable on Ioo (a n) T
  have hfi : ∀ n, IntegrableOn E (Ioo (a n) T) (volume.restrict (Ioo (0 : ℝ) T)) := by
    intro n
    have h_sub : Ioo (a n) T ⊆ Ioo (0 : ℝ) T :=
      Ioo_subset_Ioo (ha_pos n).le (le_refl T)
    have h_int : IntegrableOn E (Ioo (a n) T) :=
      hi (a n) (ha_pos n) (ha_lt_T n)
    exact h_int.restrict (t := Ioo (0 : ℝ) T)
  -- The integral bound holds for all n
  have h_bound : ∀ᶠ n in atTop, (∫ t in Ioo (a n) T, E t ∂(volume.restrict (Ioo (0 : ℝ) T))) ≤ C := by
    refine eventually_atTop.mpr ⟨0, fun n _ => ?_⟩
    have h_sub : Ioo (a n) T ⊆ Ioo (0 : ℝ) T :=
      Ioo_subset_Ioo (ha_pos n).le (le_refl T)
    have h_eq : (∫ t in Ioo (a n) T, E t ∂(volume.restrict (Ioo (0 : ℝ) T))) =
        (∫ t in Ioo (a n) T, E t) := by
      have h_meas : MeasurableSet (Ioo (a n) T) := measurableSet_Ioo
      rw [Measure.restrict_restrict h_meas, Set.inter_eq_left.mpr h_sub]
    rw [h_eq]
    exact hb (a n) (ha_pos n) (ha_lt_T n)
  -- Apply the AECover lemma
  have h_int_E : Integrable E (volume.restrict (Ioo (0 : ℝ) T)) :=
    h_cover.integrable_of_integral_bounded_of_nonneg_ae C hfi hn h_bound
  -- Convert to IntegrableOn
  rw [IntegrableOn]
  exact h_int_E

end EinsteinRelation.Correctors
