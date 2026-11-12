import EinsteinRelation.Correctors.EnergyDerivativeIntegral

open MeasureTheory
open Set
namespace EinsteinRelation.Correctors

/-- A one-sided energy derivative bound controls the final energy by its
past mean and the integrated error. Source: `paper/main.tex:798–806`;
AKM Lemma 8.2, printed pp. 305–307. -/
theorem energy_endpoint_le_average_add_error {a b : ℝ} (hab : a < b)
    {E F : ℝ → ℝ} (hE : ContinuousOn E (Set.Icc a b))
    (hF : ContinuousOn F (Set.Icc a b))
    (hF0 : ∀ t ∈ Set.Icc a b, 0 ≤ F t)
    (hd : ∀ t ∈ Set.Ioo a b, HasDerivAt E (deriv E t) t)
    (hb : ∀ t ∈ Set.Ioo a b, deriv E t ≤ F t) :
    E b ≤ (b-a)⁻¹ * (∫ t in a..b, E t) + ∫ t in a..b, F t := by
  have hab_le : a ≤ b := hab.le
  have h_pos : 0 < b - a := sub_pos.mpr hab
  have hF_int : IntervalIntegrable F volume a b :=
    hF.intervalIntegrable_of_Icc hab_le
  have hF_nonneg_ae : 0 ≤ᵐ[volume.restrict (Ioc a b)] F := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioc] with x hx
    exact hF0 x ⟨hx.1.le, hx.2⟩
  -- For each t ∈ [a,b], we have E(b) - E(t) ≤ ∫_t^b F(s) ds
  have h_bound (t : ℝ) (ht : t ∈ Icc a b) : E b - E t ≤ ∫ s in t..b, F s := by
    rcases ht with ⟨ht_left, ht_right⟩
    have hT : 0 ≤ b - t := sub_nonneg.mpr ht_right
    set f : ℝ → ℝ := fun s => E (t + s) with hf_def
    set g : ℝ → ℝ := fun s => F (t + s) with hg_def
    have hf_cont : ContinuousOn f (Icc (0 : ℝ) (b - t)) := by
      have h_maps : MapsTo (fun s => t + s) (Icc (0 : ℝ) (b - t)) (Icc a b) := by
        intro s hs
        rcases hs with ⟨hs0, hs1⟩
        have h_lower : a ≤ t + s := by linarith
        have h_upper : t + s ≤ b := by linarith
        exact ⟨h_lower, h_upper⟩
      have h_add_cont : ContinuousOn (fun s : ℝ => t + s) (Icc (0 : ℝ) (b - t)) :=
        (continuous_const.add continuous_id).continuousOn
      exact hE.comp' h_add_cont h_maps
    have hg_cont : ContinuousOn g (Icc (0 : ℝ) (b - t)) := by
      have h_maps : MapsTo (fun s => t + s) (Icc (0 : ℝ) (b - t)) (Icc a b) := by
        intro s hs
        rcases hs with ⟨hs0, hs1⟩
        have h_lower : a ≤ t + s := by linarith
        have h_upper : t + s ≤ b := by linarith
        exact ⟨h_lower, h_upper⟩
      have h_add_cont : ContinuousOn (fun s : ℝ => t + s) (Icc (0 : ℝ) (b - t)) :=
        (continuous_const.add continuous_id).continuousOn
      exact hF.comp' h_add_cont h_maps
    have hf_deriv : ∀ s ∈ Ioo (0 : ℝ) (b - t), HasDerivAt f (deriv f s) s := by
      intro s hs
      rcases hs with ⟨hs0, hs1⟩
      have hmem : t + s ∈ Ioo a b := by
        refine ⟨by linarith, ?_⟩
        linarith
      have hE_deriv : HasDerivAt E (deriv E (t + s)) (t + s) := hd (t + s) hmem
      have h_add_deriv : HasDerivAt (fun s' : ℝ => t + s') 1 s := by
        simpa using (hasDerivAt_id s).const_add t
      have h_comp : HasDerivAt (E ∘ (fun s' : ℝ => t + s')) (deriv E (t + s) * 1) s :=
        hE_deriv.comp s h_add_deriv
      have h_deriv_eq : deriv f s = deriv E (t + s) := by
        simpa [hf_def, mul_one] using h_comp.deriv
      rw [h_deriv_eq]
      simpa [hf_def, mul_one] using h_comp
    have hbound' : ∀ s ∈ Ioo (0 : ℝ) (b - t), deriv f s ≤ g s := by
      intro s hs
      rcases hs with ⟨hs0, hs1⟩
      have hmem : t + s ∈ Ioo a b := by
        refine ⟨by linarith, ?_⟩
        linarith
      have hE_deriv : HasDerivAt E (deriv E (t + s)) (t + s) := hd (t + s) hmem
      have h_add_deriv : HasDerivAt (fun s' : ℝ => t + s') 1 s := by
        simpa using (hasDerivAt_id s).const_add t
      have h_comp : HasDerivAt (E ∘ (fun s' : ℝ => t + s')) (deriv E (t + s) * 1) s :=
        hE_deriv.comp s h_add_deriv
      have h_deriv_eq : deriv f s = deriv E (t + s) := by
        simpa [hf_def, mul_one] using h_comp.deriv
      rw [hf_def, hg_def, h_deriv_eq]
      exact hb (t + s) hmem
    have h_energy := energy_derivative_integral_le hT hf_cont hg_cont hf_deriv hbound'
    have h_f_bt : f (b - t) = E b := by
      simp [hf_def]
    have h_f_0 : f 0 = E t := by
      simp [hf_def]
    have h_integral : (∫ s in (0 : ℝ)..(b - t), g s) = ∫ s in t..b, F s := by
      calc
        (∫ s in (0 : ℝ)..(b - t), g s) = (∫ s in (0 : ℝ)..(b - t), F (t + s)) := by simp [hg_def]
        _ = ∫ u in t..b, F u := by
          simpa [add_comm] using intervalIntegral.integral_comp_add_right (fun u => F u) t
    rw [h_f_bt, h_f_0, h_integral] at h_energy
    exact h_energy
  -- Now integrate the inequality over t ∈ [a,b]
  have hE_int : IntervalIntegrable E volume a b :=
    hE.intervalIntegrable_of_Icc hab_le
  have h_integrated : (∫ t in a..b, (E b - E t)) ≤ (∫ t in a..b, (∫ s in a..b, F s)) := by
    have h_int_mono (t : ℝ) (ht : t ∈ Icc a b) : E b - E t ≤ (∫ s in a..b, F s) := by
      have h := h_bound t ht
      have h_int_mono' : (∫ s in t..b, F s) ≤ (∫ s in a..b, F s) :=
        intervalIntegral.integral_mono_interval ht.1 ht.2 (le_refl b) hF_nonneg_ae hF_int
      linarith
    have h_int1 : IntervalIntegrable (fun t => E b - E t) volume a b :=
      ((intervalIntegrable_const (c := E b) (by simp)).sub hE_int)
    have h_int2 : IntervalIntegrable (fun _ => ∫ s in a..b, F s) volume a b :=
      intervalIntegrable_const (c := ∫ s in a..b, F s) (by simp)
    exact intervalIntegral.integral_mono_on hab_le h_int1 h_int2 h_int_mono
  -- Compute both sides
  have h_lhs : (∫ t in a..b, (E b - E t)) = (b - a) * E b - (∫ t in a..b, E t) := by
    calc
      (∫ t in a..b, (E b - E t)) = (∫ t in a..b, E b) - (∫ t in a..b, E t) :=
        intervalIntegral.integral_sub (intervalIntegrable_const (c := E b) (by simp)) hE_int
      _ = ((b - a) • E b) - (∫ t in a..b, E t) := by
        simp [intervalIntegral.integral_const]
      _ = (b - a) * E b - (∫ t in a..b, E t) := by simp
  have h_rhs : (∫ t in a..b, (∫ s in a..b, F s)) = (b - a) * (∫ s in a..b, F s) := by
    simp [intervalIntegral.integral_const]
  rw [h_lhs, h_rhs] at h_integrated
  -- Now we have: (b-a) * E b - ∫_a^b E ≤ (b-a) * ∫_a^b F
  -- Rearrange to get: E b ≤ (b-a)⁻¹ * ∫_a^b E + ∫_a^b F
  have h_pos_ne : b - a ≠ 0 := by linarith
  have h_ineq : (b - a) * E b - (∫ t in a..b, E t) ≤ (b - a) * (∫ s in a..b, F s) := by linarith
  have h_inv_nonneg : 0 ≤ (b - a)⁻¹ := inv_nonneg.mpr h_pos.le
  have h_final : E b ≤ (b - a)⁻¹ * (∫ t in a..b, E t) + (∫ s in a..b, F s) := by
    calc
      E b = ((b - a)⁻¹ * ((b - a) * E b)) := by field_simp [h_pos_ne]
      _ = ((b - a)⁻¹ * ((b - a) * E b - (∫ t in a..b, E t) + (∫ t in a..b, E t))) := by ring
      _ = ((b - a)⁻¹ * ((b - a) * E b - (∫ t in a..b, E t))) + (b - a)⁻¹ * (∫ t in a..b, E t) := by ring
      _ ≤ ((b - a)⁻¹ * ((b - a) * (∫ s in a..b, F s))) + (b - a)⁻¹ * (∫ t in a..b, E t) := by
        have h_mul : (b - a)⁻¹ * ((b - a) * E b - (∫ t in a..b, E t)) ≤
            (b - a)⁻¹ * ((b - a) * (∫ s in a..b, F s)) :=
          mul_le_mul_of_nonneg_left h_ineq h_inv_nonneg
        linarith
      _ = (∫ s in a..b, F s) + (b - a)⁻¹ * (∫ t in a..b, E t) := by field_simp [h_pos_ne]
      _ = (b - a)⁻¹ * (∫ t in a..b, E t) + (∫ s in a..b, F s) := by ring
  simpa [add_comm] using h_final

end EinsteinRelation.Correctors
