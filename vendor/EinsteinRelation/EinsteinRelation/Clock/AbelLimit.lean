import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.LinearCombination

/-!
# Abel limit of a Laplace transform

Deterministic input to the velocity and clock identities (`paper/main.tex`, lines 1146–1148
and 1182–1189). If `F` is measurable, satisfies `|F t| ≤ K (t + √t)` for `t ≥ 0`, and
`F t / t → η` at infinity, then `s ^ 2 * ∫_{t > 0} e^{-s t} F t → η` as `s → 0⁺`.

The substitution `u = s t` turns the average into `∫_{u > 0} e^{-u} (s F(u / s)) du`. For each
`u > 0` the integrand tends to `η u e^{-u}`. For `0 < s < 1` it is dominated by
`K (2 u + 1) e^{-u}`, which is integrable, so dominated convergence applies. The limit is
`η ∫_{u > 0} u e^{-u} du = η Γ(2) = η`.
-/

open MeasureTheory Filter Topology

namespace EinsteinRelation.Clock

/-- The scaled integrand is dominated for `0 < s < 1`. -/
private lemma norm_scaled_le (F : ℝ → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hbound : ∀ t, 0 ≤ t → |F t| ≤ K * (t + Real.sqrt t)) {s v : ℝ}
    (hs : 0 < s) (hs1 : s < 1) (hv : 0 < v) :
    ‖s * (Real.exp (-v) * F (v / s))‖ ≤ Real.exp (-v) * (K * (2 * v + 1)) := by
  have hvs : 0 ≤ v / s := div_nonneg hv.le hs.le
  have hst : s * (v / s) = v := by
    rw [mul_div_assoc', mul_div_cancel_left₀ v hs.ne']
  have hsq : Real.sqrt (v / s) ≤ 1 + v / s :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith [sq_nonneg (v / s)]⟩
  have h2 : s * Real.sqrt (v / s) ≤ s + v :=
    calc s * Real.sqrt (v / s) ≤ s * (1 + v / s) := mul_le_mul_of_nonneg_left hsq hs.le
      _ = s + v := by linear_combination hst
  have hexp : 0 < Real.exp (-v) := Real.exp_pos _
  have key : s * |F (v / s)| ≤ K * (2 * v + 1) :=
    calc s * |F (v / s)| ≤ s * (K * (v / s + Real.sqrt (v / s))) :=
          mul_le_mul_of_nonneg_left (hbound (v / s) hvs) hs.le
      _ = K * (v + s * Real.sqrt (v / s)) := by linear_combination K * hst
      _ ≤ K * (2 * v + 1) := mul_le_mul_of_nonneg_left (by linarith) hK
  rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_pos hs, abs_of_pos hexp]
  calc s * (Real.exp (-v) * |F (v / s)|) = Real.exp (-v) * (s * |F (v / s)|) := by ring
    _ ≤ Real.exp (-v) * (K * (2 * v + 1)) := mul_le_mul_of_nonneg_left key hexp.le

/-- Pointwise limit of the scaled integrand as the scale `s` decreases to `0`. -/
private lemma tendsto_scaled_pointwise (F : ℝ → ℝ) (η : ℝ)
    (hlim : Tendsto (fun t => F t / t) atTop (𝓝 η)) {v : ℝ} (hv : 0 < v) :
    Tendsto (fun s : ℝ => s * (Real.exp (-v) * F (v / s))) (𝓝[>] 0)
      (𝓝 (η * (Real.exp (-v) * v))) := by
  have hinv : Tendsto (fun s : ℝ => s⁻¹) (𝓝[>] (0 : ℝ)) atTop := tendsto_inv_nhdsGT_zero
  have hdiv : Tendsto (fun s : ℝ => v / s) (𝓝[>] 0) atTop :=
    (hinv.const_mul_atTop hv).congr fun s => (div_eq_mul_inv v s).symm
  have hq : Tendsto (fun s : ℝ => F (v / s) / (v / s)) (𝓝[>] 0) (𝓝 η) := hlim.comp hdiv
  have h3 : Tendsto (fun s : ℝ => v * (F (v / s) / (v / s))) (𝓝[>] 0) (𝓝 (v * η)) :=
    hq.const_mul v
  have h4 : Tendsto (fun s : ℝ => s * F (v / s)) (𝓝[>] 0) (𝓝 (v * η)) := by
    refine h3.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with s hs
    show v * (F (v / s) / (v / s)) = s * F (v / s)
    rw [div_div_eq_mul_div]
    linear_combination (s * F (v / s)) * mul_inv_cancel₀ hv.ne'
  have h5 : Tendsto (fun s : ℝ => Real.exp (-v) * (s * F (v / s))) (𝓝[>] 0)
      (𝓝 (Real.exp (-v) * (v * η))) := h4.const_mul (Real.exp (-v))
  have h6 : Tendsto (fun s : ℝ => s * (Real.exp (-v) * F (v / s))) (𝓝[>] 0)
      (𝓝 (Real.exp (-v) * (v * η))) := h5.congr fun s => by
    show Real.exp (-v) * (s * F (v / s)) = s * (Real.exp (-v) * F (v / s))
    ring
  have e : Real.exp (-v) * (v * η) = η * (Real.exp (-v) * v) := by ring
  rw [e] at h6
  exact h6

/-- **Abel limit.** If `F` is measurable, `|F t| ≤ K (t + √t)` for `t ≥ 0`, and `F t / t → η`,
then `s ^ 2 * ∫_{t > 0} e^{-s t} F t → η` as `s → 0⁺`. -/
theorem abel_tendsto_of_div_tendsto (F : ℝ → ℝ) (hF : Measurable F) (K η : ℝ)
    (hbound : ∀ t, 0 ≤ t → |F t| ≤ K * (t + Real.sqrt t))
    (hlim : Tendsto (fun t => F t / t) atTop (𝓝 η)) :
    Tendsto (fun s => s ^ 2 * ∫ t in Set.Ioi (0:ℝ), Real.exp (-(s * t)) * F t)
      (𝓝[>] 0) (𝓝 η) := by
  have hK : 0 ≤ K := by
    have h1 := hbound 1 zero_le_one
    rw [Real.sqrt_one] at h1
    linarith [abs_nonneg (F 1)]
  -- The Euler integral `∫_{u > 0} e^{-u} u du = Γ(2) = 1`, and integrability of its factors.
  have hI1 : IntegrableOn (fun x : ℝ => Real.exp (-x) * x) (Set.Ioi 0) := by
    refine (Real.GammaIntegral_convergent (show (0:ℝ) < 2 by norm_num)).congr_fun
      (fun x _ => ?_) measurableSet_Ioi
    show Real.exp (-x) * x ^ ((2:ℝ) - 1) = Real.exp (-x) * x
    norm_num
  have hI0 : IntegrableOn (fun x : ℝ => Real.exp (-x)) (Set.Ioi 0) := by
    refine (Real.GammaIntegral_convergent (show (0:ℝ) < 1 by norm_num)).congr_fun
      (fun x _ => ?_) measurableSet_Ioi
    show Real.exp (-x) * x ^ ((1:ℝ) - 1) = Real.exp (-x)
    norm_num
  have hG : ∫ x in Set.Ioi (0:ℝ), Real.exp (-x) * x = 1 := by
    have e : ∫ x in Set.Ioi (0:ℝ), Real.exp (-x) * x
        = ∫ x in Set.Ioi (0:ℝ), Real.exp (-x) * x ^ ((2:ℝ) - 1) :=
      setIntegral_congr_fun measurableSet_Ioi (fun x _ => by norm_num)
    rw [e, ← Real.Gamma_eq_integral (show (0:ℝ) < 2 by norm_num), Real.Gamma_two]
  -- The dominating function `e^{-v} K (2 v + 1)`.
  have hint : IntegrableOn (fun v : ℝ => Real.exp (-v) * (K * (2 * v + 1))) (Set.Ioi 0) := by
    have h : IntegrableOn (fun v : ℝ => 2 * K * (Real.exp (-v) * v) + K * Real.exp (-v))
        (Set.Ioi 0) :=
      (Integrable.const_mul hI1 (2 * K)).add (Integrable.const_mul hI0 K)
    refine h.congr_fun (fun v _ => ?_) measurableSet_Ioi
    show 2 * K * (Real.exp (-v) * v) + K * Real.exp (-v) = Real.exp (-v) * (K * (2 * v + 1))
    ring
  have hF_meas : ∀ᶠ s in 𝓝[>] (0:ℝ),
      AEStronglyMeasurable (fun v : ℝ => s * (Real.exp (-v) * F (v / s)))
        (volume.restrict (Set.Ioi (0:ℝ))) := by
    refine Filter.Eventually.of_forall fun s => ?_
    have hexp : Measurable (fun v : ℝ => Real.exp (-v)) :=
      Real.measurable_exp.comp measurable_neg
    have hdiv : Measurable (fun v : ℝ => F (v / s)) := hF.comp (measurable_id'.div_const s)
    have hmeas : Measurable (fun v : ℝ => s * (Real.exp (-v) * F (v / s))) :=
      measurable_const.mul (hexp.mul hdiv)
    exact hmeas.aestronglyMeasurable
  have h_bound : ∀ᶠ s in 𝓝[>] (0:ℝ), ∀ᵐ v ∂(volume.restrict (Set.Ioi (0:ℝ))),
      ‖s * (Real.exp (-v) * F (v / s))‖ ≤ Real.exp (-v) * (K * (2 * v + 1)) := by
    filter_upwards [Ioo_mem_nhdsGT (show (0:ℝ) < 1 by norm_num)] with s hs
    filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi (0:ℝ)))]
      with v hv
    exact norm_scaled_le F K hK hbound hs.1 hs.2 (Set.mem_Ioi.mp hv)
  have h_lim : ∀ᵐ v ∂(volume.restrict (Set.Ioi (0:ℝ))),
      Tendsto (fun s : ℝ => s * (Real.exp (-v) * F (v / s))) (𝓝[>] 0)
        (𝓝 (η * (Real.exp (-v) * v))) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioi : MeasurableSet (Set.Ioi (0:ℝ)))]
      with v hv
    exact tendsto_scaled_pointwise F η hlim (Set.mem_Ioi.mp hv)
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (fun v : ℝ => Real.exp (-v) * (K * (2 * v + 1))) hF_meas h_bound hint h_lim
  have hI : ∫ v in Set.Ioi (0:ℝ), η * (Real.exp (-v) * v) = η := by
    rw [integral_const_mul, hG, mul_one]
  rw [hI] at hDCT
  -- Change of variables `u = s t`, then the factor `s ^ 2` absorbs `s⁻¹`.
  have key : ∀ s : ℝ, 0 < s →
      s ^ 2 * (∫ t in Set.Ioi (0:ℝ), Real.exp (-(s * t)) * F t)
        = ∫ v in Set.Ioi (0:ℝ), s * (Real.exp (-v) * F (v / s)) := by
    intro s hs
    have hchange : (∫ t in Set.Ioi (0:ℝ), Real.exp (-(s * t)) * F t)
        = s⁻¹ * ∫ v in Set.Ioi (0:ℝ), Real.exp (-v) * F (v / s) := by
      have h := integral_comp_mul_left_Ioi (fun v => Real.exp (-v) * F (v / s)) 0 hs
      have hsx : ∀ x : ℝ, s * x / s = x := fun x => mul_div_cancel_left₀ x hs.ne'
      simp only [mul_zero, smul_eq_mul, hsx] at h
      exact h
    rw [hchange, integral_const_mul]
    linear_combination
      (s * ∫ v in Set.Ioi (0:ℝ), Real.exp (-v) * F (v / s)) * mul_inv_cancel₀ hs.ne'
  refine Tendsto.congr' ?_ hDCT
  filter_upwards [self_mem_nhdsWithin] with s hs
  exact (key s (Set.mem_Ioi.mp hs)).symm

/-- **Abel limit under a linear bound.** The conclusion of `abel_tendsto_of_div_tendsto` holds
when `|F t| ≤ K t` for `t ≥ 0`. -/
theorem abel_tendsto_of_bounded_rate (F : ℝ → ℝ) (hF : Measurable F) (K η : ℝ)
    (hbound : ∀ t, 0 ≤ t → |F t| ≤ K * t)
    (hlim : Tendsto (fun t => F t / t) atTop (𝓝 η)) :
    Tendsto (fun s => s ^ 2 * ∫ t in Set.Ioi (0:ℝ), Real.exp (-(s * t)) * F t)
      (𝓝[>] 0) (𝓝 η) := by
  have hK : 0 ≤ K := by
    have h1 := hbound 1 zero_le_one
    linarith [abs_nonneg (F 1)]
  refine abel_tendsto_of_div_tendsto F hF K η (fun t ht => ?_) hlim
  calc |F t| ≤ K * t := hbound t ht
    _ ≤ K * (t + Real.sqrt t) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.sqrt_nonneg t]) hK

end EinsteinRelation.Clock
