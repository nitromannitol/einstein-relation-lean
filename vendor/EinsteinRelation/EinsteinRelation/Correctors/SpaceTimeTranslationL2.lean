import EinsteinRelation.Correctors.PairedPDETimeTranslation

/-! # Strong L² continuity of full space-time translations

Source: `paper/main.tex:822–830`. The spatial energy norm of a compact
cutoff is preserved under translations, and translations tend strongly
to the identity in every space-time direction.
-/

open MeasureTheory Filter
open scoped Topology ENNReal

namespace EinsteinRelation.Correctors

/-- Full space-time translations are strongly continuous on the actual
L² field. Source: `paper/main.tex:822–830`. -/
theorem paired_tendsto_spacetime_translate_L2 {d : ℕ}
    {u : ℝ × Vec d → ℝ} (hu : MemLp u 2 volume) :
    Tendsto (fun h : ℝ × Vec d => eLpNorm
      (fun z : ℝ × Vec d => u (z + h) - u z) 2 volume) (𝓝 0) (𝓝 0) := by
  letI : (volume : Measure (ℝ × Vec d)).IsAddRightInvariant := by
    change ((volume : Measure ℝ).prod (volume : Measure (Vec d))).IsAddRightInvariant
    infer_instance
  let τ : (ℝ × Vec d) → C(ℝ × Vec d, ℝ × Vec d) :=
    fun h => ⟨fun z => z + h, continuous_id.add continuous_const⟩
  have hτ : Continuous τ :=
    ContinuousMap.continuous_of_continuous_uncurry τ (by
      change Continuous (fun p : (ℝ × Vec d) × (ℝ × Vec d) => p.2 + p.1)
      fun_prop)
  have hmp (h : ℝ × Vec d) : MeasurePreserving (τ h) volume volume :=
    measurePreserving_add_right volume h
  have hc := (continuous_const : Continuous (fun _ : ℝ × Vec d => hu.toLp u)).compMeasurePreservingLp
    hτ hmp (by norm_num : (2 : ℝ≥0∞) ≠ ∞)
  have heq (h : ℝ × Vec d) : Lp.compMeasurePreserving (τ h) (hmp h) (hu.toLp u) =
      (hu.comp_measurePreserving (hmp h)).toLp (fun z => u (z + h)) := rfl
  have hzero : Lp.compMeasurePreserving (τ 0) (hmp 0) (hu.toLp u) = hu.toLp u := by
    apply Lp.ext
    filter_upwards [Lp.coeFn_compMeasurePreserving (hu.toLp u) (hmp 0)] with z hz
    simpa only [τ, ContinuousMap.coe_mk, add_zero, Function.comp_def] using hz
  have ht := hc.continuousAt (x := 0)
  rw [ContinuousAt, hzero] at ht
  simp_rw [heq] at ht
  exact (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _
    (fun h => hu.comp_measurePreserving (hmp h)) u hu).mp ht

end EinsteinRelation.Correctors
