import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
import Mathlib.MeasureTheory.Function.UniformIntegrable

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology BigOperators
noncomputable section
namespace EinsteinFull.Blueprint

theorem holder_tendsto_eLpNorm_of_tendsto_L2
    {α ι : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] (l : Filter ι) [l.NeBot]
    (p : ℝ) (hp : 2 ≤ p) (M : ℝ≥0)
    (F : ι → α → ℂ)
    (hF : ∀ n, AEStronglyMeasurable (F n) μ)
    (hbound : ∀ᶠ n in l,
      eLpNorm (F n) (ENNReal.ofReal (2 * p)) μ ≤ (M : ℝ≥0∞))
    (h2 : Tendsto (fun n => eLpNorm (F n) 2 μ) l (𝓝 0)) :
    Tendsto (fun n => eLpNorm (F n) (ENNReal.ofReal p) μ) l (𝓝 0) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by norm_num) hp
  have hp1 : 0 < p - 1 := by linarith
  have hnorm (n : ι) (hnBound : eLpNorm (F n) (ENNReal.ofReal (2 * p)) μ ≤ (M : ℝ≥0∞)) :
      eLpNorm (F n) (ENNReal.ofReal p) μ ^ p ≤
        eLpNorm (F n) 2 μ * (M : ℝ≥0∞) ^ (p - 1) := by
    have hn := (hF n).norm
    have hg : AEStronglyMeasurable (fun x => ‖F n x‖ ^ (p - 1)) μ :=
      (Real.continuous_rpow_const hp1.le).comp_aestronglyMeasurable hn
    have hprod : (fun x => ‖F n x‖ * ‖F n x‖ ^ (p - 1)) =
        (fun x => ‖F n x‖ ^ p) := by
      funext x
      calc
        ‖F n x‖ * ‖F n x‖ ^ (p - 1) =
            ‖F n x‖ ^ 1 * ‖F n x‖ ^ (p - 1) := by rw [Real.rpow_one]
        _ = ‖F n x‖ ^ (1 + (p - 1)) :=
          (Real.rpow_add_of_nonneg (norm_nonneg _) (by norm_num) hp1.le).symm
        _ = ‖F n x‖ ^ p := by congr 1; ring
    have hc := eLpNorm'_le_eLpNorm'_mul_eLpNorm' hn hg
      (fun x y : ℝ => x * y) 1
      (Filter.Eventually.of_forall (fun x => by simp [nnnorm_mul]))
      (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) < 2)
      (by norm_num : (1 : ℝ) / 1 = 1 / 2 + 1 / 2)
    rw [hprod, eLpNorm'_norm_rpow _ _ _ hp0, one_mul,
      eLpNorm'_norm_rpow _ _ _ hp1, eLpNorm'_norm] at hc
    simp only [ENNReal.coe_one, one_mul] at hc
    have heq (q : ℝ) (hq : 0 < q) :
        eLpNorm (F n) (ENNReal.ofReal q) μ = eLpNorm' (F n) q μ := by
      rw [eLpNorm_eq_eLpNorm' (by positivity) ENNReal.ofReal_ne_top (hF n),
        ENNReal.toReal_ofReal hq.le]
    rw [heq p hp0]
    have htwo : eLpNorm (F n) 2 μ = eLpNorm' (F n) 2 μ := by
      simpa using heq 2 (by norm_num)
    rw [htwo]
    exact hc.trans (mul_le_mul_right (ENNReal.rpow_le_rpow
      ((eLpNorm'_le_eLpNorm'_of_exponent_le (by positivity : 0 < 2 * (p - 1))
        (by linarith : 2 * (p - 1) ≤ 2 * p) μ (hF n)).trans
          (by rw [← heq (2 * p) (by positivity)]; exact hnBound)) hp1.le) _)
  have hupper : Tendsto (fun n =>
      (eLpNorm (F n) 2 μ * (M : ℝ≥0∞) ^ (p - 1)) ^ (1 / p)) l (𝓝 0) := by
    have hm : (M : ℝ≥0∞) ^ (p - 1) ≠ ∞ :=
      ENNReal.rpow_ne_top_of_nonneg hp1.le ENNReal.coe_ne_top
    have hz : Tendsto (fun n => eLpNorm (F n) 2 μ * (M : ℝ≥0∞) ^ (p - 1))
        l (𝓝 0) := by simpa only [zero_mul] using ENNReal.Tendsto.mul_const h2 (Or.inr hm)
    simpa only [ENNReal.zero_rpow_of_pos (by positivity : 0 < 1 / p)] using
      hz.ennrpow_const (1 / p)
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (Filter.Eventually.of_forall (fun _ => bot_le))
  filter_upwards [hbound] with n hnBound
  have h := ENNReal.rpow_le_rpow (hnorm n hnBound) (by positivity : 0 ≤ 1 / p)
  simpa only [← ENNReal.rpow_mul, mul_one_div_cancel hp0.ne', ENNReal.rpow_one] using h
end EinsteinFull.Blueprint
