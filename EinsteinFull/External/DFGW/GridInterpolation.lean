import EinsteinFull.External.DFGW.GridScale
import EinsteinFull.External.DFGW.GridInterpolationScale
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution

/-! # Interpolation of diffusive grid limits

A limit along inverse square-root grid scales also holds at arbitrary scales when the
observation times are rounded to the corresponding grid parameter.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.External.DFGW

variable {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
variable {P : Measure Ω} [IsProbabilityMeasure P] {W : Measure Ω'} [IsProbabilityMeasure W]
variable {d m : ℕ}

/-- Interpolate a joint grid-scale limit to arbitrary scales at rounded grid parameters. -/
theorem tendstoInDistribution_floor_grid_parameter
    (N : ℝ≥0 → Ω → Vec d) (t : Fin m → ℝ≥0) (Z : Ω' → Fin m → Vec d)
    (hgrid : TendstoInDistribution (fun n η j => gridScale n •
      N (((gridScale n)⁻¹ ^ 2).toNNReal * t j) η) atTop Z (fun _ => P) W)
    (hBmeas : ∀ ε : ℝ, AEMeasurable (fun η j => ε •
      N (floorTime ((ε⁻¹ ^ 2).toNNReal) * t j) η) P) :
    TendstoInDistribution (fun (ε : ℝ) η j => ε •
      N (floorTime ((ε⁻¹ ^ 2).toNNReal) * t j) η) (𝓝[>] 0) Z (fun _ => P) W := by
  let idx := diffusiveGridIndex
  let G : ℝ → Ω → Fin m → Vec d := fun ε η j => gridScale (idx ε) •
    N (((gridScale (idx ε))⁻¹ ^ 2).toNNReal * t j) η
  let H : ℝ → Ω → Fin m → Vec d := fun ε η j => ε • N (((idx ε + 1 : ℕ) : ℝ≥0) * t j) η
  let B : ℝ → Ω → Fin m → Vec d := fun ε η j => ε •
    N (floorTime ((ε⁻¹ ^ 2).toNNReal) * t j) η
  let q : ℝ → ℝ := fun ε => ε * Real.sqrt (idx ε + 1)
  have hevent : ∀ᶠ ε in 𝓝[>] (0 : ℝ), idx ε + 1 = ⌊ε⁻¹ ^ 2⌋₊ :=
    eventually_diffusiveGridIndex_succ
  have hqmeasure : TendstoInMeasure P (fun ε _ => q ε) (𝓝[>] 0) (fun _ => 1) :=
    tendstoInMeasure_const_of_tendsto P q 1 tendsto_diffusiveGrid_ratio
  have hG : TendstoInDistribution G (𝓝[>] 0) Z (fun _ => P) W := by
    refine ⟨fun ε => hgrid.forall_aemeasurable (idx ε), hgrid.aemeasurable_limit, ?_⟩
    exact hgrid.tendsto.comp tendsto_diffusiveGridIndex
  have hprod := hG.continuous_comp_prodMk_of_tendstoInMeasure_const
    (g := fun z : (Fin m → Vec d) × ℝ => z.2 • z.1)
    (continuous_snd.smul continuous_fst) hqmeasure
      (fun _ => measurable_const.aemeasurable)
  have hH : TendstoInDistribution H (𝓝[>] 0) Z (fun _ => P) W := by
    apply TendstoInDistribution.congr (h := hprod) _ _
    · intro ε
      apply ae_of_all P
      intro η
      funext j i
      have hroot : Real.sqrt (idx ε + 1) ≠ 0 := Real.sqrt_ne_zero'.2 (by positivity)
      have htime : (((gridScale (idx ε))⁻¹ ^ 2).toNNReal) =
          ((idx ε + 1 : ℕ) : ℝ≥0) := by
        apply NNReal.eq
        rw [Real.coe_toNNReal _ (sq_nonneg _), gridScale_inv_sq]
        push_cast
        rfl
      change (ε * Real.sqrt (idx ε + 1)) * (gridScale (idx ε) *
        N (((gridScale (idx ε))⁻¹ ^ 2).toNNReal * t j) η i) =
          ε * N (((idx ε + 1 : ℕ) : ℝ≥0) * t j) η i
      rw [htime]
      simp only [gridScale]
      field_simp
    · exact ae_of_all W fun γ => by simp only [one_smul]
  change TendstoInDistribution B (𝓝[>] 0) Z (fun _ => P) W
  refine ⟨hBmeas, hH.aemeasurable_limit, ?_⟩
  apply hH.tendsto.congr'
  filter_upwards [hevent] with ε hε
  have htime : floorTime ((ε⁻¹ ^ 2).toNNReal) = ((idx ε + 1 : ℕ) : ℝ≥0) := by
    simp only [floorTime, Real.coe_toNNReal _ (sq_nonneg _), hε]
  have heq : H ε = B ε := by
    funext η j
    simp only [H, B, htime]
  rw [heq]

end EinsteinFull.External.DFGW
