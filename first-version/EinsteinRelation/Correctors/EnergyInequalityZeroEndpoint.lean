import EinsteinRelation.Correctors.WeakTimeFundamentalTheorem

open MeasureTheory Filter Topology
open intervalIntegral

namespace EinsteinRelation.Correctors

/-- An integrated energy inequality extends to zero by the continuous
trace and integrability of its two actual time integrands.
Source: `paper/main.tex:824–840`. -/
theorem energy_inequality_from_positive_endpoints {f E H : ℝ → ℝ} {T : ℝ}
    (hT : 0 ≤ T) (hf : ContinuousOn f (Set.Icc 0 T))
    (hE : IntegrableOn E (Set.Icc 0 T)) (hH : IntegrableOn H (Set.Icc 0 T))
    (hpos : ∀ a b : ℝ, 0 < a → a < b → b ≤ T →
      f b - f a + (∫ s in a..b, E s) ≤ ∫ s in a..b, H s) :
    ∀ t ∈ Set.Icc 0 T,
      f t - f 0 + (∫ s in (0 : ℝ)..t, E s) ≤ ∫ s in (0 : ℝ)..t, H s := by
  intro t ht
  rcases ht with ⟨ht0, htT⟩
  set G : ℝ → ℝ := fun s => f s - f 0 + (∫ u in (0 : ℝ)..s, E u) - (∫ u in (0 : ℝ)..s, H u) with hGdef
  have hG0 : G 0 = 0 := by
    simp [hGdef]
  have hGcont : ContinuousOn G (Set.Icc 0 T) := by
    have h_prim_E : ContinuousOn (fun s : ℝ => ∫ u in (0 : ℝ)..s, E u) (Set.Icc 0 T) := by
      have h_int : IntegrableOn E (Set.uIcc (0 : ℝ) T) := by
        rw [Set.uIcc_of_le hT]
        exact hE
      have h := continuousOn_primitive_interval h_int
      rw [Set.uIcc_of_le hT] at h
      exact h
    have h_prim_H : ContinuousOn (fun s : ℝ => ∫ u in (0 : ℝ)..s, H u) (Set.Icc 0 T) := by
      have h_int : IntegrableOn H (Set.uIcc (0 : ℝ) T) := by
        rw [Set.uIcc_of_le hT]
        exact hH
      have h := continuousOn_primitive_interval h_int
      rw [Set.uIcc_of_le hT] at h
      exact h
    exact ((hf.sub continuousOn_const).add h_prim_E).sub h_prim_H
  by_cases ht0' : t = 0
  · subst t; simp
  · have hpos_t : 0 < t := lt_of_le_of_ne ht0 (Ne.symm ht0')
    have hG_le : ∀ a, 0 < a → a < t → G t ≤ G a := by
      intro a ha ha_lt
      have haT : a ≤ T := by linarith
      have h_int0a_E : IntervalIntegrable E volume (0 : ℝ) a :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : (0 : ℝ) ≤ a)).mpr
          (hE.mono_set (Set.Icc_subset_Icc_right haT))
      have h_int0a_H : IntervalIntegrable H volume (0 : ℝ) a :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : (0 : ℝ) ≤ a)).mpr
          (hH.mono_set (Set.Icc_subset_Icc_right haT))
      have h_intat_E : IntervalIntegrable E volume a t :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : a ≤ t)).mpr
          (hE.mono_set (Set.Icc_subset_Icc (by linarith) (by linarith)))
      have h_intat_H : IntervalIntegrable H volume a t :=
        (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith : a ≤ t)).mpr
          (hH.mono_set (Set.Icc_subset_Icc (by linarith) (by linarith)))
      have h_split_E := integral_add_adjacent_intervals h_int0a_E h_intat_E
      have h_split_H := integral_add_adjacent_intervals h_int0a_H h_intat_H
      have hpos_ineq := hpos a t ha ha_lt htT
      dsimp [G]
      linarith
    have h_cont0 : ContinuousWithinAt G (Set.Icc 0 T) 0 :=
      hGcont.continuousWithinAt (by constructor; linarith; exact hT)
    have h_seq_div : Tendsto (fun n : ℕ => t / ((n : ℝ) + 2)) atTop (𝓝 0) := by
      have h := tendsto_const_div_atTop_nhds_zero_nat (C := t)
      have h_add : Tendsto (fun n : ℕ => n + 2) atTop atTop := tendsto_add_atTop_nat 2
      have h_comp := h.comp h_add
      convert h_comp using 1
      ext n
      simp [Nat.cast_add]
    have h_seq_nhdsWithin : Tendsto (fun n : ℕ => t / ((n : ℝ) + 2)) atTop
        (𝓝[Set.Icc 0 T] 0) := by
      refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ h_seq_div ?_
      filter_upwards [eventually_ge_atTop 0] with n hn
      have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
      have h_denom_nonneg : 0 ≤ (n : ℝ) + 2 := by linarith
      have h_nonneg : 0 ≤ t / ((n : ℝ) + 2) :=
        div_nonneg ht0 h_denom_nonneg
      have h_le_T : t / ((n : ℝ) + 2) ≤ T := by
        have h_denom_pos : 1 ≤ (n : ℝ) + 2 := by linarith
        refine (div_le_self ht0 h_denom_pos).trans htT
      exact ⟨h_nonneg, h_le_T⟩
    have h_Gtendsto : Tendsto (fun n : ℕ => G (t / ((n : ℝ) + 2))) atTop (𝓝 (G 0)) :=
      (show Tendsto G (𝓝[Set.Icc 0 T] 0) (𝓝 (G 0)) from h_cont0).comp h_seq_nhdsWithin
    have h_G_le_seq : ∀ n : ℕ, G t ≤ G (t / ((n : ℝ) + 2)) := by
      intro n
      apply hG_le (t / ((n : ℝ) + 2))
      · have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have hpos_denom : 0 < (n : ℝ) + 2 := by linarith
        exact div_pos hpos_t hpos_denom
      · have hn' : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        have h_denom : (1 : ℝ) < (n : ℝ) + 2 := by linarith
        exact (div_lt_self hpos_t h_denom)
    have h_Gtendsto_const : Tendsto (fun _ : ℕ => G t) atTop (𝓝 (G t)) :=
      tendsto_const_nhds
    have h_bound : (fun _ : ℕ => G t) ≤ᶠ[atTop] (fun n : ℕ => G (t / ((n : ℝ) + 2))) := by
      rw [Filter.EventuallyLE]
      simpa using (Filter.eventually_atTop.mpr ⟨(0 : ℕ), fun (n : ℕ) _ => h_G_le_seq n⟩)
    have h_nonpos : G t ≤ G 0 :=
      le_of_tendsto_of_tendsto h_Gtendsto_const h_Gtendsto h_bound
    rw [hG0] at h_nonpos
    dsimp [G] at h_nonpos
    linarith

end EinsteinRelation.Correctors
