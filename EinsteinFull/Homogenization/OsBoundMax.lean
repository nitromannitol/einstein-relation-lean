import EinsteinRelation.External.AKMEnergyDensity

/-!
# The stochastic bound of a maximum

If `X ≤ O_s(θ₁)` and `Y ≤ O_s(θ₂)` in the notation of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Appendix A, then
`max X Y ≤ O_s(2^(1/s) max θ₁ θ₂)`. The proof is the pointwise inequality
`exp(max(u, v)/2) ≤ (exp u + exp v)/2` for `u, v ≥ 0`.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.External.AKM

theorem exp_max_half_le {u v : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) :
    Real.exp (max u v / 2) ≤ (Real.exp u + Real.exp v) / 2 := by
  have key : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → b ≤ a →
      Real.exp (a / 2) ≤ (Real.exp a + Real.exp b) / 2 := by
    intro a b ha hb hba
    have h1 : Real.exp (a / 2) ^ 2 = Real.exp a := by
      rw [sq, ← Real.exp_add]
      ring_nf
    have h2 : 1 ≤ Real.exp b := Real.one_le_exp hb
    nlinarith [sq_nonneg (Real.exp (a / 2) - 1)]
  rcases le_total u v with h | h
  · rw [max_eq_right h, add_comm]
    exact key v u hv hu h
  · rw [max_eq_left h]
    exact key u v hu hv h

theorem rpow_inv_mul_max_le {θ θ₁ s m : ℝ} (hθ₁ : 0 < θ₁) (hθ : θ₁ ≤ θ) (hs : 0 < s)
    (hm : 0 ≤ m) : (θ⁻¹ * m) ^ s ≤ (θ₁⁻¹ * m) ^ s := by
  have h1 : θ⁻¹ * m ≤ θ₁⁻¹ * m :=
    mul_le_mul_of_nonneg_right (inv_anti₀ hθ₁ hθ) hm
  exact Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr (hθ₁.le.trans hθ)) hm) h1 hs.le

/-- **The stochastic bound of a maximum.** -/
theorem osBound_max {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {X Y : Ω → ℝ}
    {s θ₁ θ₂ : ℝ} (hX : OsBound P X s θ₁) (hY : OsBound P Y s θ₂) :
    OsBound P (fun ω => max (X ω) (Y ω)) s ((2 : ℝ) ^ s⁻¹ * max θ₁ θ₂) := by
  obtain ⟨hXm, hs, hθ₁, hXi⟩ := hX
  obtain ⟨hYm, -, hθ₂, hYi⟩ := hY
  set θ := max θ₁ θ₂ with hθdef
  have hθ : 0 < θ := lt_max_of_lt_left hθ₁
  have h2s : 0 < (2 : ℝ) ^ s⁻¹ := Real.rpow_pos_of_pos two_pos _
  refine ⟨hXm.max hYm, hs, mul_pos h2s hθ, ?_⟩
  have hpt : ∀ ω, Real.exp ((((2 : ℝ) ^ s⁻¹ * θ)⁻¹ * max (max (X ω) (Y ω)) 0) ^ s) ≤
      (Real.exp ((θ₁⁻¹ * max (X ω) 0) ^ s) + Real.exp ((θ₂⁻¹ * max (Y ω) 0) ^ s)) / 2 := by
    intro ω
    set a := max (X ω) 0
    set b := max (Y ω) 0
    have ha : 0 ≤ a := le_max_right _ _
    have hb : 0 ≤ b := le_max_right _ _
    have hmax : max (max (X ω) (Y ω)) 0 = max a b := by
      simp only [a, b]
      rcases le_total (X ω) (Y ω) with h | h
      · rw [max_eq_right h, max_eq_right (max_le_max h le_rfl)]
      · rw [max_eq_left h, max_eq_left (max_le_max h le_rfl)]
    have hscale : (((2 : ℝ) ^ s⁻¹ * θ)⁻¹ * max a b) ^ s = (θ⁻¹ * max a b) ^ s / 2 := by
      rw [mul_inv, mul_assoc, Real.mul_rpow (inv_nonneg.mpr h2s.le)
        (mul_nonneg (inv_nonneg.mpr hθ.le) (le_max_of_le_left ha)), Real.inv_rpow h2s.le,
        ← Real.rpow_mul two_pos.le, inv_mul_cancel₀ hs.ne', Real.rpow_one]
      ring
    have hmaxs : (θ⁻¹ * max a b) ^ s = max ((θ⁻¹ * a) ^ s) ((θ⁻¹ * b) ^ s) := by
      rcases le_total a b with h | h
      · rw [max_eq_right h, max_eq_right (Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr hθ.le) ha)
          (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hθ.le)) hs.le)]
      · rw [max_eq_left h, max_eq_left (Real.rpow_le_rpow (mul_nonneg (inv_nonneg.mpr hθ.le) hb)
          (mul_le_mul_of_nonneg_left h (inv_nonneg.mpr hθ.le)) hs.le)]
    rw [hmax, hscale, hmaxs]
    have hu := rpow_inv_mul_max_le hθ₁ (le_max_left θ₁ θ₂) hs ha
    have hv := rpow_inv_mul_max_le hθ₂ (le_max_right θ₁ θ₂) hs hb
    have hu0 : 0 ≤ (θ⁻¹ * a) ^ s := Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr hθ.le) ha) _
    have hv0 : 0 ≤ (θ⁻¹ * b) ^ s := Real.rpow_nonneg (mul_nonneg (inv_nonneg.mpr hθ.le) hb) _
    refine (exp_max_half_le hu0 hv0).trans ?_
    gcongr
  have hmX : Measurable (fun ω => ENNReal.ofReal (Real.exp ((θ₁⁻¹ * max (X ω) 0) ^ s))) := by
    fun_prop
  have hmY : Measurable (fun ω => ENNReal.ofReal (Real.exp ((θ₂⁻¹ * max (Y ω) 0) ^ s))) := by
    fun_prop
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp ((((2 : ℝ) ^ s⁻¹ * θ)⁻¹ *
        max (max (X ω) (Y ω)) 0) ^ s)) ∂P
      ≤ ∫⁻ ω, (2 : ℝ≥0∞)⁻¹ * (ENNReal.ofReal (Real.exp ((θ₁⁻¹ * max (X ω) 0) ^ s)) +
          ENNReal.ofReal (Real.exp ((θ₂⁻¹ * max (Y ω) 0) ^ s))) ∂P := by
        refine lintegral_mono fun ω => ?_
        rw [← ENNReal.ofReal_add (Real.exp_pos _).le (Real.exp_pos _).le,
          ← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_inv_of_pos two_pos,
          ← ENNReal.ofReal_mul (by norm_num)]
        refine ENNReal.ofReal_le_ofReal ((hpt ω).trans (le_of_eq ?_))
        ring
    _ = (2 : ℝ≥0∞)⁻¹ * ((∫⁻ ω, ENNReal.ofReal (Real.exp ((θ₁⁻¹ * max (X ω) 0) ^ s)) ∂P) +
          ∫⁻ ω, ENNReal.ofReal (Real.exp ((θ₂⁻¹ * max (Y ω) 0) ^ s)) ∂P) := by
        rw [lintegral_const_mul' _ _ (by simp), lintegral_add_left hmX]
    _ ≤ (2 : ℝ≥0∞)⁻¹ * (2 + 2) := by gcongr
    _ = 2 := by
        rw [← two_mul, ← mul_assoc, ENNReal.inv_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
          one_mul]

end EinsteinFull.Homogenization
