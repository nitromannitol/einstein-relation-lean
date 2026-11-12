import EinsteinRelation.Correctors.PairedPDEHilbertRegularization
import EinsteinRelation.Correctors.PairedPDESmoothRegularization
import Mathlib.MeasureTheory.Group.Prod

/-! # Scalar representatives of the Hilbert-space kernel averages

Source: `paper/main.tex:832–840`. Fubini identifies actual scalar
convolutions with averages of translated L² classes.
-/

open MeasureTheory Filter
open scoped Topology ENNReal Convolution

noncomputable section
namespace EinsteinRelation.Correctors

private instance volume_addRightInvariant (d : ℕ) :
    (volume : Measure (ℝ × Vec d)).IsAddRightInvariant := by
  change ((volume : Measure ℝ).prod (volume : Measure (Vec d))).IsAddRightInvariant
  infer_instance

/-- Absolute integrability of the actual convolution pairing.
Source: `paper/main.tex:832–840`. -/
theorem paired_integrable_kernel_pairing {d : ℕ}
    {u f ρ : ℝ × Vec d → ℝ}
    (hu : MemLp u 2 volume) (hf : MemLp f 2 volume) (hρ : Integrable ρ volume) :
    Integrable (fun p : (ℝ × Vec d) × (ℝ × Vec d) =>
      ρ p.1 * (f p.2 * u (p.2 - p.1))) (volume.prod volume) := by
  have hmp := measurePreserving_prod_sub (volume : Measure (ℝ × Vec d))
    (volume : Measure (ℝ × Vec d))
  have ha := hρ.norm.mul_prod hf.integrable_sq
  have hb := hmp.integrable_comp_of_integrable (hρ.norm.mul_prod hu.integrable_sq)
  have hm := hρ.aestronglyMeasurable.comp_fst.mul
    (hf.aestronglyMeasurable.comp_snd.mul
      (hu.aestronglyMeasurable.comp_snd.comp_measurePreserving hmp))
  refine ((ha.add hb).div_const 2).mono' hm (Filter.Eventually.of_forall fun p => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  change |ρ p.1| * (|f p.2| * |u (p.2 - p.1)|) ≤
    (|ρ p.1| * (f p.2)^2 + |ρ p.1| * (u (p.2 - p.1))^2) / 2
  have hh : |f p.2| * |u (p.2 - p.1)| ≤ ((f p.2)^2 + (u (p.2 - p.1))^2) / 2 := by
    nlinarith [sq_nonneg (|f p.2| - |u (p.2 - p.1)|), sq_abs (f p.2),
      sq_abs (u (p.2 - p.1))]
  nlinarith [mul_le_mul_of_nonneg_left hh (abs_nonneg (ρ p.1))]

/-- The actual scalar convolution represents the Bochner average in L².
Source: `paper/main.tex:832–840`. -/
theorem paired_convolution_toLp_eq_average {d : ℕ}
    {u ρ : ℝ × Vec d → ℝ} (hu : MemLp u 2 volume)
    (hρ : Continuous ρ) (hρc : HasCompactSupport ρ)
    (hC : MemLp (fun z : ℝ × Vec d => ∫ w : ℝ × Vec d, ρ w * u (z - w)) 2 volume) :
    hC.toLp (fun z : ℝ × Vec d => ∫ w : ℝ × Vec d, ρ w * u (z - w)) =
      ∫ w : ℝ × Vec d, ρ w • pairedSpacetimeTranslateLp (hu.toLp u) (-w) := by
  have hA : Integrable (fun w : ℝ × Vec d =>
      ρ w • pairedSpacetimeTranslateLp (hu.toLp u) (-w)) volume :=
    (hρ.smul ((paired_continuous_spacetimeTranslateLp (hu.toLp u)).comp
      continuous_neg)).integrable_of_hasCompactSupport hρc.smul_right
  apply ext_inner_left ℝ
  intro q
  rw [← integral_inner hA]
  have hid (w : ℝ × Vec d) :
      inner ℝ q (pairedSpacetimeTranslateLp (hu.toLp u) (-w)) =
        ∫ z : ℝ × Vec d, q z * u (z - w) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_compMeasurePreserving (hu.toLp u)
      (measurePreserving_add_right (volume : Measure (ℝ × Vec d)) (-w)),
      (measurePreserving_add_right (volume : Measure (ℝ × Vec d)) (-w)).quasiMeasurePreserving.ae_eq
        hu.coeFn_toLp] with z hz huz
    change (hu.toLp u) (z + -w) = u (z + -w) at huz
    change (pairedSpacetimeTranslateLp (hu.toLp u) (-w)) z = (hu.toLp u) (z + -w) at hz
    simp only [hz, huz, RCLike.inner_apply, conj_trivial,
      sub_eq_add_neg, mul_comm]
  simp_rw [inner_smul_right, hid, ← integral_const_mul]
  have hp := paired_integrable_kernel_pairing hu (Lp.memLp q)
    (hρ.integrable_of_hasCompactSupport hρc)
  rw [integral_integral_swap hp]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hC.coeFn_toLp] with z hz
  rw [hz]
  simp only [RCLike.inner_apply, conj_trivial]
  rw [← integral_mul_const]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun w => by ring

/-- Strong approximation of actual scalar convolutions whenever their
L² membership is known. Source: `paper/main.tex:832–840`. -/
theorem paired_tendsto_scalar_convolution_L2 {d : ℕ}
    {u : ℝ × Vec d → ℝ} (hu : MemLp u 2 volume)
    {ρ : ℕ → ℝ × Vec d → ℝ}
    (hρ : ∀ k, Continuous (ρ k)) (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k z, 0 ≤ ρ k z) (hρ1 : ∀ k, (∫ z, ρ k z) = 1)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hsupp : ∀ k, Function.support (ρ k) ⊆ Metric.closedBall 0 (ε k))
    (hC : ∀ k, MemLp
      (fun z : ℝ × Vec d => ∫ w : ℝ × Vec d, ρ k w * u (z - w)) 2 volume) :
    Tendsto (fun k => eLpNorm
      (fun z : ℝ × Vec d => (∫ w : ℝ × Vec d, ρ k w * u (z - w)) - u z)
        2 volume) atTop (𝓝 0) := by
  apply (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' _ hC u hu).mp
  simpa only [paired_convolution_toLp_eq_average hu (hρ _) (hρc _) (hC _)] using
    paired_tendsto_L2_kernel_average (hu.toLp u) hρ0 hρ1 hε hsupp

/-- Compactly supported energy data have actual smooth L² convolutions.
Source: `paper/main.tex:832–840`. -/
theorem paired_compact_convolution_memLp {d : ℕ}
    {u ρ : ℝ × Vec d → ℝ} (hu : MemLp u 2 volume)
    (huc : HasCompactSupport u) (hρ : ContDiff ℝ (⊤ : ℕ∞) ρ)
    (hρc : HasCompactSupport ρ) :
    MemLp (fun z : ℝ × Vec d => ∫ w : ℝ × Vec d, u w * ρ (z - w)) 2 volume := by
  obtain ⟨hc, hcc, _⟩ := paired_convolution_test_admissible hu huc hρ hρc
    (Set.subset_univ _)
  exact hc.continuous.memLp_of_hasCompactSupport hcc

/-- Approximation limits for the actual compact energy field and its
compact product-rule derivatives. Source: `paper/main.tex:832–840`. -/
theorem paired_tendsto_compact_convolution_L2 {d : ℕ}
    {u : ℝ × Vec d → ℝ} (hu : MemLp u 2 volume) (huc : HasCompactSupport u)
    {ρ : ℕ → ℝ × Vec d → ℝ}
    (hρ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (ρ k))
    (hρc : ∀ k, HasCompactSupport (ρ k))
    (hρ0 : ∀ k z, 0 ≤ ρ k z) (hρ1 : ∀ k, (∫ z, ρ k z) = 1)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hsupp : ∀ k, Function.support (ρ k) ⊆ Metric.closedBall 0 (ε k)) :
    Tendsto (fun k => eLpNorm
      (fun z : ℝ × Vec d => (∫ w : ℝ × Vec d, u w * ρ k (z - w)) - u z)
        2 volume) atTop (𝓝 0) := by
  letI : (volume : Measure (ℝ × Vec d)).IsAddLeftInvariant := by
    change ((volume : Measure ℝ).prod (volume : Measure (Vec d))).IsAddLeftInvariant
    infer_instance
  letI : Measure.IsAddHaarMeasure (volume : Measure (ℝ × Vec d)) :=
    Measure.prod.instIsAddHaarMeasure (volume : Measure ℝ) (volume : Measure (Vec d))
  have heq (k : ℕ) (z : ℝ × Vec d) :
      (∫ w : ℝ × Vec d, u w * ρ k (z - w)) =
        ∫ w : ℝ × Vec d, ρ k w * u (z - w) := by
    change (u ⋆[ContinuousLinearMap.mul ℝ ℝ, volume] ρ k) z = _
    rw [convolution_mul_swap]
    exact integral_congr_ae (Filter.Eventually.of_forall fun _ => mul_comm _ _)
  have hC (k : ℕ) : MemLp
      (fun z : ℝ × Vec d => ∫ w : ℝ × Vec d, ρ k w * u (z - w)) 2 volume := by
    simpa only [← heq] using paired_compact_convolution_memLp hu huc (hρ k) (hρc k)
  simpa only [heq] using paired_tendsto_scalar_convolution_L2 hu
    (fun k => (hρ k).continuous) hρc hρ0 hρ1 hε hsupp hC

end EinsteinRelation.Correctors
