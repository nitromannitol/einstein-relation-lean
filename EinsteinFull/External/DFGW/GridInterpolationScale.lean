import EinsteinFull.External.DFGW.DiffusiveGrid

/-! # Normalization at diffusive grid indices

The integer grid parameter agrees eventually with the rounded inverse square, and the
corresponding normalization converges to one.
-/

open MeasureTheory Filter
open scoped ENNReal Topology

namespace EinsteinFull.External.DFGW

/-- The grid index plus one eventually equals the rounded inverse square. -/
theorem eventually_diffusiveGridIndex_succ :
    ∀ᶠ ε in 𝓝[>] (0 : ℝ), diffusiveGridIndex ε + 1 = ⌊ε⁻¹ ^ 2⌋₊ := by
  filter_upwards [tendsto_diffusiveGridIndex.eventually (eventually_ge_atTop 1)] with ε hε
  dsimp only [diffusiveGridIndex] at hε ⊢
  omega

/-- The ratio between a scale and its grid scale converges to one. -/
theorem tendsto_diffusiveGrid_ratio :
    Tendsto (fun ε : ℝ => ε * Real.sqrt (diffusiveGridIndex ε + 1)) (𝓝[>] 0) (𝓝 1) := by
  apply tendsto_diffusiveFloor_sqrt.congr'
  filter_upwards [eventually_diffusiveGridIndex_succ] with ε hε
  have hcast : (⌊ε⁻¹ ^ 2⌋₊ : ℝ) = (diffusiveGridIndex ε : ℝ) + 1 := by
    exact_mod_cast hε.symm
  simp only [hcast]

/-- Deterministic convergence yields convergence in measure for constant random variables. -/
theorem tendstoInMeasure_const_of_tendsto {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (q : ℝ → ℝ) (x : ℝ) (hq : Tendsto q (𝓝[>] 0) (𝓝 x)) :
    TendstoInMeasure P (fun ε _ => q ε) (𝓝[>] 0) (fun _ => x) := by
  apply tendstoInMeasure_iff_dist.mpr
  intro δ hδ
  have hsmall : ∀ᶠ ε in 𝓝[>] (0 : ℝ), dist (q ε) x < δ :=
    (Metric.tendsto_nhds.mp hq) δ hδ
  have hzero : ∀ᶠ ε in 𝓝[>] (0 : ℝ), P {η : Ω | δ ≤ dist (q ε) x} = 0 := by
    filter_upwards [hsmall] with ε hε
    have hempty : {η : Ω | δ ≤ dist (q ε) x} = ∅ := by
      ext η
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact not_le_of_gt hε
    rw [hempty, measure_empty]
  have heq : (fun ε => P {η : Ω | δ ≤ dist (q ε) x}) =ᶠ[𝓝[>] (0 : ℝ)]
      fun _ => (0 : ℝ≥0∞) := hzero
  exact tendsto_const_nhds.congr' heq.symm

end EinsteinFull.External.DFGW
