import EinsteinRelation.External.AKMEnergyDensity
import Mathlib.MeasureTheory.Function.L2Space

/-! Real moment and L2 consequences of the source stretched-exponential convention.
These estimates are proved internally for every positive stochastic exponent. -/

open MeasureTheory
namespace EinsteinFull.AKM
open EinsteinRelation.External.AKM

/-- A scaled real power is dominated by its stretched exponential. -/
theorem abs_rpow_le_stretched_exp {x θ s p : ℝ}
    (hθ : 0 < θ) (hs : 0 < s) (hp : 0 < p) :
    |x| ^ p ≤ (θ ^ p * (p / s) ^ (p / s)) *
      Real.exp ((θ⁻¹ * |x|) ^ s) := by
  let t := θ⁻¹ * |x|
  have ht : 0 ≤ t := mul_nonneg (inv_nonneg.mpr hθ.le) (abs_nonneg x)
  have hscale : |x| = θ * t := by dsimp only [t]; field_simp
  have hpower : (t ^ s) ^ (p / s) = t ^ p := by
    rw [← Real.rpow_mul ht, mul_div_cancel₀ p hs.ne']
  have hdom := rpow_le_exp_mul (Real.rpow_nonneg ht s) (div_pos hp hs)
  rw [hpower] at hdom
  calc |x| ^ p = θ ^ p * t ^ p := by rw [hscale, Real.mul_rpow hθ.le ht]
       _ ≤ θ ^ p * ((p / s) ^ (p / s) * Real.exp (t ^ s)) :=
         mul_le_mul_of_nonneg_left hdom (Real.rpow_nonneg hθ.le p)
       _ = _ := by ring

/-- Every positive real moment follows from the source O_s bound.
No probability normalization or restriction s>=1 is needed. -/
theorem abs_moment_le_of_osBound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {s θ p : ℝ}
    (h : OsBound P (fun ω => |X ω|) s θ) (hp : 0 < p) :
    (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂P) ≤
      ENNReal.ofReal (2 * θ ^ p * (p / s) ^ (p / s)) := by
  have hθ : 0 < θ := h.2.2.1
  have hs : 0 < s := h.2.1
  have hC : 0 ≤ θ ^ p * (p / s) ^ (p / s) :=
    mul_nonneg (Real.rpow_nonneg hθ.le p) (Real.rpow_nonneg (div_nonneg hp.le hs.le) _)
  have hExp : (∫⁻ ω, ENNReal.ofReal
      (Real.exp ((θ⁻¹ * |X ω|) ^ s)) ∂P) ≤ 2 := by
    simpa only [max_eq_left (abs_nonneg (X _))] using h.2.2.2
  calc (∫⁻ ω, ENNReal.ofReal (|X ω| ^ p) ∂P) ≤
      ∫⁻ ω, ENNReal.ofReal ((θ ^ p * (p / s) ^ (p / s)) *
        Real.exp ((θ⁻¹ * |X ω|) ^ s)) ∂P :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal
          (abs_rpow_le_stretched_exp hθ hs hp)
    _ = ENNReal.ofReal (θ ^ p * (p / s) ^ (p / s)) *
        (∫⁻ ω, ENNReal.ofReal (Real.exp ((θ⁻¹ * |X ω|) ^ s)) ∂P) := by
      simp_rw [ENNReal.ofReal_mul hC]
      exact lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (θ ^ p * (p / s) ^ (p / s)) * 2 := mul_le_mul_right hExp _
    _ = _ := by
      rw [show 2 * θ ^ p * (p / s) ^ (p / s) =
        (θ ^ p * (p / s) ^ (p / s)) * 2 by ring,
        ENNReal.ofReal_mul hC, ENNReal.ofReal_ofNat]

/-- The source stretched-exponential estimate implies genuine L2 membership.
Measurability of the signed variable is retained explicitly. -/
theorem memLp_two_of_osBound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {s θ : ℝ}
    (h : OsBound P (fun ω => |X ω|) s θ) (hX : AEStronglyMeasurable X P) :
    MemLp X 2 P := by
  apply (memLp_two_iff_integrable_sq_norm hX).mpr
  refine ⟨hX.norm.pow 2, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall fun ω => sq_nonneg ‖X ω‖)]
  have hm := abs_moment_le_of_osBound h (show (0 : ℝ) < 2 by norm_num)
  simp only [Real.rpow_two, Real.norm_eq_abs] at hm ⊢
  exact lt_of_le_of_lt hm ENNReal.ofReal_lt_top

/-- Quantitative real L2 integral bound, with its exact source scale factor. -/
theorem integral_sq_le_of_osBound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {s θ : ℝ}
    (h : OsBound P (fun ω => |X ω|) s θ) :
    (∫ ω, |X ω| ^ 2 ∂P) ≤ 2 * θ ^ 2 * (2 / s) ^ (2 / s) := by
  have hm := abs_moment_le_of_osBound h (show (0 : ℝ) < 2 by norm_num)
  simp only [Real.rpow_two] at hm
  rw [integral_eq_lintegral_of_nonneg_ae
    (Filter.Eventually.of_forall fun ω => sq_nonneg |X ω|) (h.1.pow_const 2).aestronglyMeasurable]
  have hC : 0 ≤ 2 * θ ^ 2 * (2 / s) ^ (2 / s) :=
    mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg θ))
      (Real.rpow_nonneg (div_nonneg (by norm_num) h.2.1.le) _)
  simpa only [ENNReal.toReal_ofReal hC]
    using ENNReal.toReal_mono ENNReal.ofReal_ne_top hm

/-- The source O_s scale becomes an explicit linear L2 bound. -/
theorem sqrt_integral_sq_le_of_osBound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} {X : Ω → ℝ} {s θ : ℝ}
    (h : OsBound P (fun ω => |X ω|) s θ) :
    Real.sqrt (∫ ω, |X ω| ^ 2 ∂P) ≤
      Real.sqrt (2 * (2 / s) ^ (2 / s)) * θ := by
  have hC : 0 ≤ 2 * (2 / s) ^ (2 / s) :=
    mul_nonneg (by norm_num) (Real.rpow_nonneg (div_nonneg (by norm_num) h.2.1.le) _)
  calc Real.sqrt (∫ ω, |X ω| ^ 2 ∂P) ≤
      Real.sqrt (2 * θ ^ 2 * (2 / s) ^ (2 / s)) :=
        Real.sqrt_le_sqrt (integral_sq_le_of_osBound h)
    _ = Real.sqrt (2 * (2 / s) ^ (2 / s)) * θ := by
      rw [show 2 * θ ^ 2 * (2 / s) ^ (2 / s) =
        (2 * (2 / s) ^ (2 / s)) * θ ^ 2 by ring,
        Real.sqrt_mul hC, Real.sqrt_sq_eq_abs, abs_of_pos h.2.2.1]

end EinsteinFull.AKM
