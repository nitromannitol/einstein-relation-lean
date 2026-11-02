import EinsteinRelation.Correctors.PairedPDESpaceTimeTranslation
import Mathlib.Analysis.Convolution

/-! # Strong convergence of kernel averages in the actual Hilbert space

Source: `paper/main.tex:822–830`. Continuous translations of the L² class
can be averaged as Bochner integrals. Shrinking positive kernels converge
strongly to that class.
-/

open MeasureTheory Filter Metric
open scoped Topology ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

private instance volume_addRightInvariant (d : ℕ) :
    (volume : Measure (ℝ × Vec d)).IsAddRightInvariant := by
  change ((volume : Measure ℝ).prod (volume : Measure (Vec d))).IsAddRightInvariant
  infer_instance

private instance volume_addLeftInvariant (d : ℕ) :
    (volume : Measure (ℝ × Vec d)).IsAddLeftInvariant := by
  change ((volume : Measure ℝ).prod (volume : Measure (Vec d))).IsAddLeftInvariant
  infer_instance

/-- Translation of the space-time L² class, for compact regularization.
Source: `paper/main.tex:822–830`. -/
def pairedSpacetimeTranslateLp {d : ℕ} (f : Lp ℝ 2 (volume : Measure (ℝ × Vec d)))
    (h : ℝ × Vec d) : Lp ℝ 2 (volume : Measure (ℝ × Vec d)) :=
  Lp.compMeasurePreserving (fun z => z + h) (measurePreserving_add_right volume h) f

/-- The actual translated L² classes form a continuous Hilbert-space path.
Source: `paper/main.tex:822–830`. -/
theorem paired_continuous_spacetimeTranslateLp {d : ℕ}
    (f : Lp ℝ 2 (volume : Measure (ℝ × Vec d))) :
    Continuous (pairedSpacetimeTranslateLp f) := by
  let τ : (ℝ × Vec d) → C(ℝ × Vec d, ℝ × Vec d) :=
    fun h => ⟨fun z => z + h, continuous_id.add continuous_const⟩
  have hτ : Continuous τ :=
    ContinuousMap.continuous_of_continuous_uncurry τ (by
      change Continuous (fun p : (ℝ × Vec d) × (ℝ × Vec d) => p.2 + p.1)
      fun_prop)
  exact (continuous_const : Continuous (fun _ : ℝ × Vec d => f)).compMeasurePreservingLp
    hτ (fun h => measurePreserving_add_right volume h) (by norm_num)

/-- Zero translation preserves the actual class. Source: `paper/main.tex:822–830`. -/
theorem paired_spacetimeTranslateLp_zero {d : ℕ}
    (f : Lp ℝ 2 (volume : Measure (ℝ × Vec d))) : pairedSpacetimeTranslateLp f 0 = f := by
  apply Lp.ext
  change (fun z => (Lp.compMeasurePreserving (fun z => z + (0 : ℝ × Vec d))
    (measurePreserving_add_right volume 0) f) z) =ᵐ[volume] fun z => f z
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (measurePreserving_add_right (volume : Measure (ℝ × Vec d)) 0)] with z hz
  simpa only [add_zero, Function.comp_def] using hz

/-- Shrinking support gives the small-set condition for an approximate
identity. Source: `paper/main.tex:822–830`. -/
theorem paired_tendsto_kernel_support {d : ℕ} {ρ : ℕ → ℝ × Vec d → ℝ}
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hsupp : ∀ k, Function.support (ρ k) ⊆ closedBall 0 (ε k)) :
    Tendsto (fun k => Function.support (ρ k)) atTop (𝓝 (0 : ℝ × Vec d)).smallSets := by
  rw [tendsto_smallSets_iff]
  intro V hV
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  filter_upwards [hε.eventually (gt_mem_nhds hδ)] with k hk
  intro z hz
  apply hδV
  exact (closedBall_subset_ball hk) (hsupp k hz)

/-- Positive normalized kernels converge strongly when applied to the
actual L² class. Source: `paper/main.tex:822–830`. -/
theorem paired_tendsto_L2_kernel_average {d : ℕ}
    (f : Lp ℝ 2 (volume : Measure (ℝ × Vec d)))
    {ρ : ℕ → ℝ × Vec d → ℝ} (hρ0 : ∀ k z, 0 ≤ ρ k z)
    (hρ1 : ∀ k, (∫ z, ρ k z) = 1)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hsupp : ∀ k, Function.support (ρ k) ⊆ closedBall 0 (ε k)) :
    Tendsto (fun k => ∫ w : ℝ × Vec d, ρ k w • pairedSpacetimeTranslateLp f (-w))
      atTop (𝓝 f) := by
  have hc := paired_continuous_spacetimeTranslateLp f
  have ht := convolution_tendsto_right (μ := (volume : Measure (ℝ × Vec d)))
    (g := fun _ : ℕ => pairedSpacetimeTranslateLp f) (k := fun _ => 0)
    (Eventually.of_forall hρ0) (Eventually.of_forall hρ1)
    (paired_tendsto_kernel_support hε hsupp)
    (Eventually.of_forall fun _ => hc.aestronglyMeasurable)
    (hc.continuousAt.tendsto.comp tendsto_snd) tendsto_const_nhds
  simpa only [convolution_def, ContinuousLinearMap.lsmul_apply, zero_sub,
    paired_spacetimeTranslateLp_zero] using ht

end EinsteinRelation.Correctors
