import EinsteinRelation.Mobility.CorrectorGradientMoments
open MeasureTheory
open scoped ENNReal

open Real

namespace EinsteinRelation.Correctors
/-- Source: `paper/main.tex:718-723,743-745`. Probability integration
of two nonnegative random amplitudes, with all constants explicit. -/
theorem lintegral_rpow_le_of_two_majorants
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (u a b : Ω → ℝ) (K p B D : ℝ) (hK : 0 ≤ K) (hp : 0 ≤ p)
    (ha : ∀ ω, 0 ≤ a ω) (hb : ∀ ω, 0 ≤ b ω)
    (ham : AEMeasurable a P) (hbm : AEMeasurable b P)
    (hu : ∀ᵐ ω ∂P, 0 ≤ u ω ∧ u ω ≤ K * (a ω + b ω))
    (hB : (∫⁻ ω, ENNReal.ofReal (a ω ^ p) ∂P) ≤ ENNReal.ofReal B)
    (hD : (∫⁻ ω, ENNReal.ofReal (b ω ^ p) ∂P) ≤ ENNReal.ofReal D) :
    (∫⁻ ω, ENNReal.ofReal (u ω ^ p) ∂P) ≤
      ENNReal.ofReal (K ^ p * 2 ^ p * (max B 0 + max D 0)) := by
  have ha_add_b (ω) : 0 ≤ a ω + b ω := add_nonneg (ha ω) (hb ω)
  have ha_pow_nonneg (ω) : 0 ≤ a ω ^ p := Real.rpow_nonneg (ha ω) p
  have hb_pow_nonneg (ω) : 0 ≤ b ω ^ p := Real.rpow_nonneg (hb ω) p
  have hKp_nonneg : 0 ≤ K ^ p := Real.rpow_nonneg hK p
  have h2p_nonneg : 0 ≤ (2 : ℝ) ^ p := Real.rpow_nonneg (by norm_num : 0 ≤ (2 : ℝ)) p
  have hKp_mul_h2p_nonneg : 0 ≤ K ^ p * (2 : ℝ) ^ p := mul_nonneg hKp_nonneg h2p_nonneg
  have ha_pow_aemeas : AEMeasurable (fun ω => a ω ^ p) P :=
    (continuous_rpow_const hp).measurable.comp_aemeasurable ham
  have hb_pow_aemeas : AEMeasurable (fun ω => b ω ^ p) P :=
    (continuous_rpow_const hp).measurable.comp_aemeasurable hbm
  have ha_enorm_pow (ω) : ENNReal.ofReal (a ω ^ p) = (ENNReal.ofReal (a ω)) ^ p := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (ha ω) hp]
  have hb_enorm_pow (ω) : ENNReal.ofReal (b ω ^ p) = (ENNReal.ofReal (b ω)) ^ p := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (hb ω) hp]
  have hsum_enorm_pow (ω) : ENNReal.ofReal ((a ω + b ω) ^ p) =
      (ENNReal.ofReal (a ω) + ENNReal.ofReal (b ω)) ^ p := by
    rw [← ENNReal.ofReal_rpow_of_nonneg (ha_add_b ω) hp,
      ENNReal.ofReal_add (ha ω) (hb ω)]
  have ha_enorm_aemeas : AEMeasurable (fun ω => ENNReal.ofReal (a ω ^ p)) P := by
    have h : AEMeasurable (fun ω => (ENNReal.ofReal (a ω)) ^ p) P :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (ham.ennreal_ofReal)
    refine h.congr ?_
    filter_upwards [] with ω
    simp [ENNReal.ofReal_rpow_of_nonneg (ha ω) hp]
  have hb_enorm_aemeas : AEMeasurable (fun ω => ENNReal.ofReal (b ω ^ p)) P := by
    have h : AEMeasurable (fun ω => (ENNReal.ofReal (b ω)) ^ p) P :=
      ENNReal.continuous_rpow_const.measurable.comp_aemeasurable (hbm.ennreal_ofReal)
    refine h.congr ?_
    filter_upwards [] with ω
    simp [ENNReal.ofReal_rpow_of_nonneg (hb ω) hp]
  have hab_pow_aemeas : AEMeasurable (fun ω => a ω ^ p + b ω ^ p) P :=
    ha_pow_aemeas.add hb_pow_aemeas
  have hab_enorm_aemeas : AEMeasurable (fun ω => ENNReal.ofReal (a ω ^ p + b ω ^ p)) P :=
    hab_pow_aemeas.ennreal_ofReal
  have h_enorm_a_add_b_pow_le : ∀ᵐ ω ∂P,
      ENNReal.ofReal ((a ω + b ω) ^ p) ≤ ENNReal.ofReal (2 ^ p * (a ω ^ p + b ω ^ p)) := by
    filter_upwards [] with ω
    calc
      ENNReal.ofReal ((a ω + b ω) ^ p) = (ENNReal.ofReal (a ω) + ENNReal.ofReal (b ω)) ^ p := hsum_enorm_pow ω
      _ ≤ 2 ^ p * ((ENNReal.ofReal (a ω)) ^ p + (ENNReal.ofReal (b ω)) ^ p) :=
        ENNReal.add_rpow_le_two_rpow_mul_rpow_add_rpow (ENNReal.ofReal (a ω)) (ENNReal.ofReal (b ω)) hp
      _ = 2 ^ p * (ENNReal.ofReal (a ω ^ p) + ENNReal.ofReal (b ω ^ p)) := by rw [ha_enorm_pow ω, hb_enorm_pow ω]
      _ = ENNReal.ofReal (2 ^ p * (a ω ^ p + b ω ^ p)) := by
        calc
          2 ^ p * (ENNReal.ofReal (a ω ^ p) + ENNReal.ofReal (b ω ^ p))
              = (ENNReal.ofReal ((2 : ℝ) ^ p)) * (ENNReal.ofReal (a ω ^ p) + ENNReal.ofReal (b ω ^ p)) := by
            calc
              2 ^ p * (ENNReal.ofReal (a ω ^ p) + ENNReal.ofReal (b ω ^ p))
                  = ((2 : ℝ≥0∞) ^ p) * (ENNReal.ofReal (a ω ^ p) + ENNReal.ofReal (b ω ^ p)) := rfl
              _ = (ENNReal.ofReal (2 : ℝ) ^ p) * (ENNReal.ofReal (a ω ^ p) + ENNReal.ofReal (b ω ^ p)) := by norm_cast
              _ = ENNReal.ofReal ((2 : ℝ) ^ p) * (ENNReal.ofReal (a ω ^ p) + ENNReal.ofReal (b ω ^ p)) := by
                rw [ENNReal.ofReal_rpow_of_nonneg (by norm_num : 0 ≤ (2 : ℝ)) hp]
          _ = ENNReal.ofReal ((2 : ℝ) ^ p) * ENNReal.ofReal (a ω ^ p + b ω ^ p) := by
            rw [ENNReal.ofReal_add (ha_pow_nonneg ω) (hb_pow_nonneg ω)]
          _ = ENNReal.ofReal ((2 : ℝ) ^ p * (a ω ^ p + b ω ^ p)) := by
            rw [ENNReal.ofReal_mul h2p_nonneg]
  have h_enorm_u_pow_le : ∀ᵐ ω ∂P,
      ENNReal.ofReal (u ω ^ p) ≤ ENNReal.ofReal (K ^ p * 2 ^ p * (a ω ^ p + b ω ^ p)) := by
    filter_upwards [hu, h_enorm_a_add_b_pow_le] with ω ⟨hu_nonneg, hu_le⟩ h_ineq
    calc
      ENNReal.ofReal (u ω ^ p) ≤ ENNReal.ofReal ((K * (a ω + b ω)) ^ p) :=
        ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hu_nonneg hu_le hp)
      _ = ENNReal.ofReal (K ^ p * (a ω + b ω) ^ p) := by
        rw [Real.mul_rpow hK (ha_add_b ω)]
      _ = ENNReal.ofReal (K ^ p) * ENNReal.ofReal ((a ω + b ω) ^ p) := by
        rw [ENNReal.ofReal_mul hKp_nonneg]
      _ ≤ ENNReal.ofReal (K ^ p) * ENNReal.ofReal (2 ^ p * (a ω ^ p + b ω ^ p)) :=
        mul_le_mul_of_nonneg_left h_ineq (zero_le _)
      _ = ENNReal.ofReal (K ^ p * 2 ^ p * (a ω ^ p + b ω ^ p)) := by
        calc
          ENNReal.ofReal (K ^ p) * ENNReal.ofReal (2 ^ p * (a ω ^ p + b ω ^ p))
              = ENNReal.ofReal (K ^ p) * (ENNReal.ofReal (2 ^ p) * ENNReal.ofReal (a ω ^ p + b ω ^ p)) := by
            rw [ENNReal.ofReal_mul h2p_nonneg]
          _ = (ENNReal.ofReal (K ^ p) * ENNReal.ofReal (2 ^ p)) * ENNReal.ofReal (a ω ^ p + b ω ^ p) := by
            rw [mul_assoc]
          _ = ENNReal.ofReal (K ^ p * 2 ^ p) * ENNReal.ofReal (a ω ^ p + b ω ^ p) := by
            rw [← ENNReal.ofReal_mul hKp_nonneg]
          _ = ENNReal.ofReal (K ^ p * 2 ^ p * (a ω ^ p + b ω ^ p)) := by
            rw [← ENNReal.ofReal_mul hKp_mul_h2p_nonneg]
  calc
    (∫⁻ ω, ENNReal.ofReal (u ω ^ p) ∂P) ≤
        (∫⁻ ω, ENNReal.ofReal (K ^ p * 2 ^ p * (a ω ^ p + b ω ^ p)) ∂P) :=
      lintegral_mono_ae h_enorm_u_pow_le
    _ = (∫⁻ ω, ENNReal.ofReal (K ^ p * 2 ^ p) * ENNReal.ofReal (a ω ^ p + b ω ^ p) ∂P) := by
      refine lintegral_congr_ae ?_
      filter_upwards [] with ω
      rw [ENNReal.ofReal_mul hKp_mul_h2p_nonneg]
    _ = ENNReal.ofReal (K ^ p * 2 ^ p) * (∫⁻ ω, ENNReal.ofReal (a ω ^ p + b ω ^ p) ∂P) := by
      rw [lintegral_const_mul'' _ hab_enorm_aemeas]
    _ = ENNReal.ofReal (K ^ p * 2 ^ p) * (∫⁻ ω, (ENNReal.ofReal (a ω ^ p) + ENNReal.ofReal (b ω ^ p)) ∂P) := by
      congr 1
      refine lintegral_congr_ae ?_
      filter_upwards [] with ω
      simp [ENNReal.ofReal_add (ha_pow_nonneg ω) (hb_pow_nonneg ω)]
    _ = ENNReal.ofReal (K ^ p * 2 ^ p) * ((∫⁻ ω, ENNReal.ofReal (a ω ^ p) ∂P) +
        (∫⁻ ω, ENNReal.ofReal (b ω ^ p) ∂P)) := by
      rw [lintegral_add_left' ha_enorm_aemeas (fun ω => ENNReal.ofReal (b ω ^ p))]
    _ ≤ ENNReal.ofReal (K ^ p * 2 ^ p) * (ENNReal.ofReal B + ENNReal.ofReal D) := by
      gcongr
    _ ≤ ENNReal.ofReal (K ^ p * 2 ^ p) * (ENNReal.ofReal (max B 0) + ENNReal.ofReal (max D 0)) := by
      have hKp2p_nonneg : 0 ≤ ENNReal.ofReal (K ^ p * 2 ^ p) := zero_le _
      refine mul_le_mul_of_nonneg_left ?_ hKp2p_nonneg
      refine add_le_add ?_ ?_
      · exact ENNReal.ofReal_le_ofReal (le_max_left B 0)
      · exact ENNReal.ofReal_le_ofReal (le_max_left D 0)
    _ = ENNReal.ofReal (K ^ p * 2 ^ p) * ENNReal.ofReal (max B 0 + max D 0) := by
      rw [← ENNReal.ofReal_add (le_max_right B 0) (le_max_right D 0)]
    _ = ENNReal.ofReal (K ^ p * 2 ^ p * (max B 0 + max D 0)) := by
      rw [ENNReal.ofReal_mul hKp_mul_h2p_nonneg]

end EinsteinRelation.Correctors
