import EinsteinRelation.Correctors.PairedPDECutoffEnergyClass
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.MetricSpace.Thickening

/-! # Actual admissible regularizations of a localized energy field

Source: `paper/main.tex:832–840`. A compact cutoff of the actual weak
solution is globally square integrable. Convolution with a sufficiently
small normalized smooth bump gives a smooth test supported in the original
open cylinder. This construction does not claim convergence of time
derivatives of the weak solution.
-/

open MeasureTheory Metric
open scoped Pointwise ENNReal

namespace EinsteinRelation.Correctors

open External.AKM Environment.AKMTestIntegralSupport

/-- The actual cutoff field is globally L², even when the solution has only
local energy bounds. Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_cutoff_memLp_global {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : MeasurableSet U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : Continuous ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ I ×ˢ U) :
    MemLp (fun z => ζ z * u z) 2 volume := by
  have hm : MemLp (fun z => ζ z * u z) 2 (volume.restrict (I ×ˢ U)) :=
    hsol.1.mul' (hζ.memLp_top_of_hasCompactSupport hζc _)
  have heq : (I ×ˢ U).indicator (fun z => ζ z * u z) = fun z => ζ z * u z := by
    funext z
    by_cases hz : z ∈ I ×ˢ U
    · exact Set.indicator_of_mem hz _
    · rw [Set.indicator_of_notMem hz]
      have hnot : z ∉ tsupport ζ := fun hx => hz (hζsupp hx)
      rw [image_eq_zero_of_notMem_tsupport hnot, zero_mul]
  rw [← heq]
  exact (memLp_indicator_iff_restrict (hI.prod hU)).mpr hm

/-- Compactly supported L² data convolved with a smooth compact kernel
give a genuine smooth compact test, with explicit support control.
Source: `paper/main.tex:832–840`. -/
theorem paired_convolution_test_admissible {d : ℕ}
    {f ρ : ℝ × Vec d → ℝ} (hf : MemLp f 2 volume)
    (hfc : HasCompactSupport f) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) {V : Set (ℝ × Vec d)}
    (hsupp : tsupport f + tsupport ρ ⊆ V) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => ∫ w : ℝ × Vec d, f w * ρ (z - w)) ∧
      HasCompactSupport (fun z => ∫ w : ℝ × Vec d, f w * ρ (z - w)) ∧
      tsupport (fun z => ∫ w : ℝ × Vec d, f w * ρ (z - w)) ⊆ V := by
  let L := ContinuousLinearMap.mul ℝ ℝ
  have hc := hρc.contDiff_convolution_right (L := L) (hf.locallyIntegrable (by norm_num)) hρ
  have hcompact := hfc.convolution (L := L) (μ := volume) hρc
  refine ⟨hc, hcompact, ?_⟩
  apply Set.Subset.trans ?_ hsupp
  exact closure_minimal
    ((support_convolution_subset (μ := volume) L).trans
      (Set.add_subset_add subset_closure subset_closure))
    (hfc.isCompact.add hρc).isClosed

/-- The actual energy-class cutoff admits normalized smooth regularizations
at every prescribed upper scale, supported in the same open cylinder.
Source: `paper/main.tex:832–840`. -/
theorem parabolicSolution_exists_smooth_cutoff_test {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ} {U : Set (Vec d)}
    (hI : MeasurableSet I) (hU : IsOpen U)
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A I U u G)
    {ζ : ℝ × Vec d → ℝ} (hζ : ContDiff ℝ (⊤ : ℕ∞) ζ)
    (hζc : HasCompactSupport ζ) (hζsupp : tsupport ζ ⊆ interior I ×ˢ U)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ ρ : ℝ × Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) ρ ∧ HasCompactSupport ρ ∧
      (∀ z, 0 ≤ ρ z) ∧ (∀ z, ρ (-z) = ρ z) ∧ (∫ z, ρ z) = 1 ∧
      tsupport ρ ⊆ closedBall 0 ε ∧
      ContDiff ℝ (⊤ : ℕ∞) (fun z => ∫ w : ℝ × Vec d, ζ w * u w * ρ (z - w)) ∧
      HasCompactSupport (fun z => ∫ w : ℝ × Vec d, ζ w * u w * ρ (z - w)) ∧
      tsupport (fun z => ∫ w : ℝ × Vec d, ζ w * u w * ρ (z - w)) ⊆
        interior I ×ˢ U := by
  obtain ⟨δ, hδ, hδV⟩ := hζc.isCompact.exists_cthickening_subset_open
    (isOpen_interior.prod hU) hζsupp
  let r := min δ ε
  have hr : 0 < r := lt_min hδ hε
  let b : ContDiffBump (0 : ℝ × Vec d) := ⟨r / 2, r, half_pos hr, half_lt_self hr⟩
  let ρ := b.normed volume
  have hs : tsupport (fun z => ζ z * u z) + tsupport ρ ⊆ interior I ×ˢ U := by
    rintro z ⟨x, hx, y, hy, rfl⟩
    apply hδV
    apply mem_cthickening_of_dist_le (x + y) x δ (tsupport ζ)
      (tsupport_mul_subset_left hx)
    have hy' : ‖y‖ ≤ r := by
      simpa only [ρ, b.tsupport_normed_eq, mem_closedBall_zero_iff] using hy
    simpa only [dist_eq_norm, add_sub_cancel_left] using hy'.trans (min_le_left δ ε)
  have hf := parabolicSolution_cutoff_memLp_global hI hU.measurableSet hsol hζ.continuous
    hζc (hζsupp.trans (Set.prod_mono interior_subset Set.Subset.rfl))
  obtain ⟨hc, hcc, hcs⟩ := paired_convolution_test_admissible hf hζc.mul_right
    b.contDiff_normed b.hasCompactSupport_normed hs
  refine ⟨ρ, b.contDiff_normed, b.hasCompactSupport_normed, b.nonneg_normed,
    b.normed_neg, b.integral_normed, ?_, hc, hcc, hcs⟩
  rw [show tsupport ρ = closedBall 0 r from b.tsupport_normed_eq]
  exact closedBall_subset_closedBall (min_le_right δ ε)

end EinsteinRelation.Correctors
