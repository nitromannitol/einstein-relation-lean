import PDEFoundation.Measure.ShrinkingAxisBoxCollar
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Shrinking collars of product slabs

An integrable density has vanishing integral on either end collar of a
product slab when the collar width tends to zero.
-/

open Filter MeasureTheory Set
open scoped Topology

namespace EinsteinFull.Regeneration

/-- An integrable density has vanishing integral on shrinking left collars. -/
theorem tendsto_integral_left_product_collar {Z E : Type*} [MeasurableSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Measure Z) [IsFiniteMeasure ν] (a b : ℝ) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hδb : ∀ n, a + δ n ≤ b)
    (f : ℝ × Z → E) (hf : Integrable f ((volume.restrict (Icc a b)).prod ν)) :
    Tendsto (fun n => ∫ p, f p ∂((volume.restrict (Icc a (a + δ n))).prod ν))
      atTop (𝓝 0) := by
  let μ := (volume.restrict (Icc a b)).prod ν
  let S : ℕ → Set (ℝ × Z) := fun n => Ioc a (a + δ n) ×ˢ univ
  have hlim : Tendsto (fun n => ∫ p in S n, f p ∂μ) atTop (𝓝 0) := by
    apply PDE.tendsto_setIntegral_of_integrable_of_eventually_not_mem hf S
    · exact fun _ => measurableSet_Ioc.prod MeasurableSet.univ
    · intro p
      by_cases hp : a < p.1
      · have hpos : 0 < p.1 - a := by linarith
        filter_upwards [hδ.eventually_lt_const hpos] with n hn
        intro hnmem
        have := hnmem.1.2
        linarith
      · exact Eventually.of_forall fun _ hnmem => hp hnmem.1.1
  have hmeasure (n : ℕ) : μ.restrict (S n) =
      (volume.restrict (Icc a (a + δ n))).prod ν := by
    dsimp [μ, S]
    rw [← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_restrict measurableSet_Ioc]
    have hinter : Ioc a (a + δ n) ∩ Icc a b = Ioc a (a + δ n) := by
      apply inter_eq_self_of_subset_left
      intro t ht
      exact ⟨ht.1.le, ht.2.trans (hδb n)⟩
    rw [hinter, Measure.restrict_congr_set Ioc_ae_eq_Icc]
  simpa only [hmeasure] using hlim

/-- An integrable density has vanishing integral on shrinking right collars. -/
theorem tendsto_integral_right_product_collar {Z E : Type*} [MeasurableSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (ν : Measure Z) [IsFiniteMeasure ν] (a b : ℝ) (δ : ℕ → ℝ)
    (hδ : Tendsto δ atTop (𝓝 0)) (hδb : ∀ n, a ≤ b - δ n)
    (f : ℝ × Z → E) (hf : Integrable f ((volume.restrict (Icc a b)).prod ν)) :
    Tendsto (fun n => ∫ p, f p ∂((volume.restrict (Icc (b - δ n) b)).prod ν))
      atTop (𝓝 0) := by
  let μ := (volume.restrict (Icc a b)).prod ν
  let S : ℕ → Set (ℝ × Z) := fun n => Ico (b - δ n) b ×ˢ univ
  have hlim : Tendsto (fun n => ∫ p in S n, f p ∂μ) atTop (𝓝 0) := by
    apply PDE.tendsto_setIntegral_of_integrable_of_eventually_not_mem hf S
    · exact fun _ => measurableSet_Ico.prod MeasurableSet.univ
    · intro p
      by_cases hp : p.1 < b
      · have hpos : 0 < b - p.1 := by linarith
        filter_upwards [hδ.eventually_lt_const hpos] with n hn
        intro hnmem
        have := hnmem.1.1
        linarith
      · exact Eventually.of_forall fun _ hnmem => hp hnmem.1.2
  have hmeasure (n : ℕ) : μ.restrict (S n) =
      (volume.restrict (Icc (b - δ n) b)).prod ν := by
    dsimp [μ, S]
    rw [← Measure.prod_restrict, Measure.restrict_univ, Measure.restrict_restrict measurableSet_Ico]
    have hinter : Ico (b - δ n) b ∩ Icc a b = Ico (b - δ n) b := by
      apply inter_eq_self_of_subset_left
      intro t ht
      exact ⟨(hδb n).trans ht.1, ht.2.le⟩
    rw [hinter, Measure.restrict_congr_set Ico_ae_eq_Icc]
  simpa only [hmeasure] using hlim

end EinsteinFull.Regeneration
