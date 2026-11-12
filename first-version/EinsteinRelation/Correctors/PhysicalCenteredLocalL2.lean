import EinsteinRelation.Correctors.PhysicalLocalL2Moments

/-! Source: `paper/main.tex:724-731`. Transport of a local L² moment
whose additive gauge is chosen at the local center. Only measurability
of that oscillation is used, so no joint measurability of a raw scalar
potential is required. -/
open MeasureTheory
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- A local moment with a fixed center-dependent gauge transports through
a measure preserving map and a positive spatial dilation. -/
theorem root_integral_centered_moment_measurePreserving_inv_dilation
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    {P : Measure Ω} {Q : Measure Ξ} {T : Ω → Ξ}
    (hT : MeasurePreserving T P Q) {d : ℕ}
    (F : Ξ → Vec d → ℝ) (r c R p : ℝ) (z : Vec d)
    (hr : 1 ≤ r) (hc : 0 ≤ c) (hR : R ≤ 4) (hp : 0 ≤ p)
    (hF : ∀ a x, 0 ≤ F a x)
    (hi : ∀ᵐ a ∂Q, IntegrableOn (F a) (ball (r⁻¹ • z) 4) volume)
    (hm : AEMeasurable (fun a => ENNReal.ofReal
      ((Real.sqrt (∫ x in ball (r⁻¹ • z) 4, F a x ∂volume)) ^ p)) Q)
    (B : ℝ≥0∞)
    (hb : (∫⁻ a, ENNReal.ofReal
      ((Real.sqrt (∫ x in ball (r⁻¹ • z) 4, F a x ∂volume)) ^ p) ∂Q) ≤ B) :
    (∫⁻ ω, ENNReal.ofReal ((Real.sqrt
      (∫ x in ball z R, c * F (T ω) (r⁻¹ • x) ∂volume)) ^ p) ∂P) ≤
      ENNReal.ofReal ((Real.sqrt (c * r ^ d)) ^ p) * B := by
  have hr0 : 0 < r := zero_lt_one.trans_le hr
  have hrad : r⁻¹ * R ≤ 4 := by
    calc
      _ ≤ r⁻¹ * 4 := mul_le_mul_of_nonneg_left hR (inv_nonneg.mpr hr0.le)
      _ ≤ 1 * 4 := mul_le_mul_of_nonneg_right (inv_le_one_of_one_le₀ hr) (by norm_num)
      _ = _ := by norm_num
  have hsub : ball (r⁻¹ • z) (r⁻¹ * R) ⊆ ball (r⁻¹ • z) 4 :=
    fun _ hx => lt_of_lt_of_le hx hrad
  have hmap : (∫⁻ ω, ENNReal.ofReal
      ((Real.sqrt (∫ x in ball (r⁻¹ • z) 4, F (T ω) x ∂volume)) ^ p) ∂P) ≤ B := by
    rw [← hT.map_eq] at hb hm
    exact (lintegral_map' hm hT.measurable.aemeasurable).symm.le.trans hb
  apply le_trans ?_ (mul_le_mul_right hmap _)
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  apply lintegral_mono_ae
  filter_upwards [hT.quasiMeasurePreserving.ae hi] with ω hω
  have hlocal : (∫ x in ball z R, c * F (T ω) (r⁻¹ • x) ∂volume) ≤
      c * r ^ d * ∫ x in ball (r⁻¹ • z) 4, F (T ω) x ∂volume := by
    rw [integral_const_mul, setIntegral_euclideanBall_inv_smul _ r R hr0 z]
    calc
      _ = (c * r ^ d) * ∫ x in ball (r⁻¹ • z) (r⁻¹ * R), F (T ω) x ∂volume := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (setIntegral_mono_set hω (ae_of_all _ fun x => hF (T ω) x)
          (Filter.Eventually.of_forall hsub)) (by positivity)
  rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ (Real.sqrt (c * r ^ d)) ^ p)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ (Real.sqrt (c * r ^ d * ∫ x in ball (r⁻¹ • z) 4, F (T ω) x ∂volume)) ^ p :=
      Real.rpow_le_rpow (Real.sqrt_nonneg _) (Real.sqrt_le_sqrt hlocal) hp
    _ = (Real.sqrt (c * r ^ d)) ^ p *
        (Real.sqrt (∫ x in ball (r⁻¹ • z) 4, F (T ω) x ∂volume)) ^ p := by
      rw [Real.sqrt_mul (by positivity : 0 ≤ c * r ^ d),
        Real.mul_rpow (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)]

end EinsteinRelation.Correctors
