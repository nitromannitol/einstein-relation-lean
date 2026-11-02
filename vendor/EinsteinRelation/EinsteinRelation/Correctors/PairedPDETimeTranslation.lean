import EinsteinRelation.Correctors.PairedPDEMultiplierConvergence
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-! # Strong continuity of time translations

Source: `paper/main.tex:822–830`. Temporal regularization of the energy-class
solution converges in the actual space-time L² norm.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

/-- Strong L² continuity of actual time translations on space-time
Lebesgue measure. Source: `paper/main.tex:822–830`. -/
theorem paired_tendsto_time_translate_L2 {d : ℕ}
    {u : ℝ × Vec d → ℝ} (hu : MemLp u 2 volume) :
    Tendsto (fun h : ℝ => eLpNorm
      (fun z : ℝ × Vec d => u (z + (h, 0)) - u z) 2 volume) (𝓝 0) (𝓝 0) := by
  letI : (volume : Measure (ℝ × Vec d)).IsAddRightInvariant := by
    change ((volume : Measure ℝ).prod (volume : Measure (Vec d))).IsAddRightInvariant
    infer_instance
  let τ : ℝ → C(ℝ × Vec d, ℝ × Vec d) :=
    fun h => ⟨fun z => z + (h, 0), continuous_id.add continuous_const⟩
  have hτ : Continuous τ :=
    ContinuousMap.continuous_of_continuous_uncurry τ (by
      change Continuous (fun p : ℝ × (ℝ × Vec d) => p.2 + (p.1, 0))
      fun_prop)
  have hmp (h : ℝ) : MeasurePreserving (τ h) volume volume :=
    measurePreserving_add_right volume (h, 0)
  have hc := (continuous_const : Continuous (fun _ : ℝ => hu.toLp u)).compMeasurePreservingLp hτ hmp
    (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have heq (h : ℝ) : Lp.compMeasurePreserving (τ h) (hmp h) (hu.toLp u) =
      (hu.comp_measurePreserving (hmp h)).toLp (fun z => u (z + (h, 0))) := rfl
  have hzero : Lp.compMeasurePreserving (τ 0) (hmp 0) (hu.toLp u) = hu.toLp u := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (hu.toLp u) (hmp 0)] with z hz
    change _ = (hu.toLp u) (z + (0 : ℝ × Vec d)) at hz
    simpa only [add_zero] using hz
  have ht := hc.continuousAt (x := 0)
  rw [ContinuousAt, hzero] at ht
  simp_rw [heq] at ht
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
    (fun h => hu.comp_measurePreserving (hmp h)) u hu).mp ht

end EinsteinRelation.Correctors
