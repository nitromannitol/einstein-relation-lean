import EinsteinRelation.External.AKMHeatKernel
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Joint continuity of bounded probability-kernel averages

Source: AKM Proposition E.1, (E.3)–(E.4), pp. 499–501;
`paper/main.tex:787–792,850`. Positivity, mass one, and pointwise
continuity give L¹ continuity by the minimum-kernel argument.
-/

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors

/-- Continuous nonnegative probability kernels act continuously on bounded data.
The proof uses the fixed integrable kernel to dominate the minimum of two kernels. -/
theorem massOneKernel_average_continuousOn {T : Type*}
    [TopologicalSpace T] [FirstCountableTopology T] {S : Set T} {d : ℕ}
    {P : T → Vec d → ℝ} {f : Vec d → ℝ}
    (hP : ∀ y, ContinuousOn (fun t => P t y) S)
    (hi : ∀ t, t ∈ S → Integrable (P t) volume)
    (hp : ∀ t, t ∈ S → ∀ y, 0 ≤ P t y)
    (hm : ∀ t, t ∈ S → (∫ y, P t y ∂volume) = 1)
    (hf : AEStronglyMeasurable f volume) {B : ℝ}
    (hB : ∀ᵐ y ∂volume, |f y| ≤ B) :
    ContinuousOn (fun t => ∫ y, P t y * f y ∂volume) S := by
  intro t ht
  have hminm (s : T) (hs : s ∈ S) :
      AEStronglyMeasurable (fun y => min (P s y) (P t y)) volume :=
    continuous_min.comp_aestronglyMeasurable
      ((hi s hs).aestronglyMeasurable.prodMk (hi t ht).aestronglyMeasurable)
  have hmini (s : T) (hs : s ∈ S) :
      Integrable (fun y => min (P s y) (P t y)) volume := by
    apply (hi t ht).mono' (hminm s hs)
    filter_upwards with y
    rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp s hs y) (hp t ht y))]
    exact min_le_right _ _
  have hmin : Tendsto (fun s => ∫ y, min (P s y) (P t y) ∂volume)
      (nhdsWithin t S) (𝓝 1) := by
    rw [← hm t ht]
    apply tendsto_integral_filter_of_dominated_convergence (P t)
    · filter_upwards [self_mem_nhdsWithin] with s hs
      exact hminm s hs
    · filter_upwards [self_mem_nhdsWithin] with s hs
      filter_upwards with y
      rw [Real.norm_eq_abs, abs_of_nonneg (le_min (hp s hs y) (hp t ht y))]
      exact min_le_right _ _
    · exact hi t ht
    · filter_upwards with y
      simpa only [min_self] using ((hP y t ht).tendsto.min
        (tendsto_const_nhds : Tendsto (fun _ : T => P t y)
          (nhdsWithin t S) (𝓝 (P t y))))
  have hid (s : T) (hs : s ∈ S) :
      (∫ y, |P s y - P t y| ∂volume) =
        2 - 2 * ∫ y, min (P s y) (P t y) ∂volume := by
    have hpt : (fun y => |P s y - P t y|) =
        (fun y => (P s y + P t y) - 2 * min (P s y) (P t y)) := by
      funext y
      rcases le_total (P s y) (P t y) with h | h
      · rw [min_eq_left h, abs_of_nonpos (sub_nonpos.mpr h)]; ring
      · rw [min_eq_right h, abs_of_nonneg (sub_nonneg.mpr h)]; ring
    rw [hpt]
    calc
      _ = (∫ y, P s y + P t y ∂volume) -
          ∫ y, 2 * min (P s y) (P t y) ∂volume :=
        integral_sub ((hi s hs).add (hi t ht)) ((hmini s hs).const_mul 2)
      _ = _ := by
        rw [integral_add (hi s hs) (hi t ht), integral_const_mul, hm s hs, hm t ht]
        ring
  have hL1 : Tendsto (fun s => ∫ y, |P s y - P t y| ∂volume)
      (nhdsWithin t S) (𝓝 0) := by
    have hh := (tendsto_const_nhds : Tendsto (fun _ : T => (2 : ℝ))
      (nhdsWithin t S) (𝓝 2)).sub (hmin.const_mul 2)
    have hh' : Tendsto (fun s => 2 - 2 * ∫ y, min (P s y) (P t y) ∂volume)
        (nhdsWithin t S) (𝓝 0) := by simpa using hh
    apply hh'.congr'
    filter_upwards [self_mem_nhdsWithin] with s hs
    exact (hid s hs).symm
  have hfb : ∀ᵐ y ∂volume, ‖f y‖ ≤ |B| := by
    filter_upwards [hB] with y hy
    exact (by simpa only [Real.norm_eq_abs] using hy.trans (le_abs_self B))
  have hif (s : T) (hs : s ∈ S) : Integrable (fun y => P s y * f y) volume :=
    (hi s hs).mul_bdd hf hfb
  have hbound : ∀ᶠ s in nhdsWithin t S,
      ‖(∫ y, P s y * f y ∂volume) - ∫ y, P t y * f y ∂volume‖ ≤
        |B| * ∫ y, |P s y - P t y| ∂volume := by
    filter_upwards [self_mem_nhdsWithin] with s hs
    have hidiff : (∫ y, P s y * f y ∂volume) - ∫ y, P t y * f y ∂volume =
        ∫ y, (P s y - P t y) * f y ∂volume := by
      rw [← integral_sub (hif s hs) (hif t ht)]
      apply integral_congr_ae
      filter_upwards with y
      ring
    rw [hidiff]
    calc
      ‖∫ y, (P s y - P t y) * f y ∂volume‖ ≤
          ∫ y, ‖(P s y - P t y) * f y‖ ∂volume := norm_integral_le_integral_norm _
      _ ≤ ∫ y, |P s y - P t y| * |B| ∂volume := by
        apply integral_mono_ae (((hi s hs).sub (hi t ht)).mul_bdd hf hfb).norm
          (((hi s hs).sub (hi t ht)).abs.mul_const |B|)
        filter_upwards [hfb] with y hy
        simpa only [norm_mul, Real.norm_eq_abs] using
          mul_le_mul_of_nonneg_left hy (abs_nonneg (P s y - P t y))
      _ = |B| * ∫ y, |P s y - P t y| ∂volume := by
        rw [integral_mul_const, mul_comm]
  apply (tendsto_iff_norm_sub_tendsto_zero).mpr
  exact squeeze_zero' (Filter.Eventually.of_forall (fun _ => norm_nonneg _)) hbound
    (by simpa using hL1.const_mul |B|)


open External.AKM Environment.AKMTestIntegralSupport
/-- The bounded scalar evolution defined by an E.1 kernel is jointly
continuous at positive times. Source: AKM (E.3)–(E.4), pp. 499–501;
`paper/main.tex:787–792,850`. -/
theorem akm_heatKernel_scalar_average_joint_continuousOn
    {d : ℕ} {K : ℝ} {A : Coefficient d K}
    {P : ℝ → Vec d → Vec d → ℝ}
    {X Y : ℝ → Vec d → Vec d → Vec d}
    {H : ℝ → Vec d → Vec d → Mat d} {C : ℝ → ℝ}
    (hP : HeatKernelProperties A P X Y H C)
    {f : Vec d → ℝ} (hf : AEStronglyMeasurable f volume)
    {B : ℝ} (hB : ∀ᵐ y ∂volume, |f y| ≤ B) :
    ContinuousOn (fun z : ℝ × Vec d => ∫ y, P z.1 z.2 y*f y ∂volume)
      (Set.Ioi 0 ×ˢ Set.univ) := by
  apply massOneKernel_average_continuousOn
    (P := fun z : ℝ × Vec d => P z.1 z.2) _ _ _ _ hf hB
  · intro y
    exact hP.1.comp
      ((continuous_fst.prodMk (continuous_snd.prodMk continuous_const)).continuousOn)
      (fun z hz => ⟨hz.1,Set.mem_univ _⟩)
  · intro z hz
    exact (hP.2.2.2.2.2.1 z.1 hz.1 z.2).1
  · intro z hz y
    exact hP.2.1 z.1 hz.1 z.2 y
  · intro z hz
    exact (hP.2.2.2.2.2.1 z.1 hz.1 z.2).2.1
end EinsteinRelation.Correctors
