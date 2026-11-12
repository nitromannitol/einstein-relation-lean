import EinsteinRelation.Correctors.OneSidedTimeMollifier
import Mathlib.Analysis.Convolution

open MeasureTheory Filter
open scoped Topology Convolution
namespace EinsteinRelation.Correctors

/-- A shrinking one-sided probability average recovers the continuous endpoint
value on its actual finite time interval. Source: `paper/main.tex:798–806`. -/
theorem tendsto_one_sided_interval_average {a b : ℝ} (hab : a < b)
    {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    {ρ : ℕ → ℝ → ℝ} (hρ0 : ∀ k s, 0 ≤ ρ k s)
    (hρ1 : ∀ k, (∫ s, ρ k s) = 1)
    {ε : ℕ → ℝ} (hε : Tendsto ε atTop (𝓝 0))
    (hεb : ∀ k, ε k ≤ (b-a)/2)
    (hsupp : ∀ k, tsupport (ρ k) ⊆ Set.Ioo 0 (ε k)) :
    Tendsto (fun k => ∫ s in Set.Ioo a b, ρ k (b-s) * f s)
      atTop (𝓝 (f b)) := by
  let c : ℝ → ℝ := fun s => max a (min s b)
  have hc : Continuous c := continuous_const.max (continuous_id.min continuous_const)
  have hcm s : c s ∈ Set.Icc a b := by
    exact ⟨le_max_left _ _,max_le hab.le (min_le_right _ _)⟩
  have hceq {s : ℝ} (hs : s ∈ Set.Icc a b) : c s = s := by
    simp only [c,min_eq_left hs.2,max_eq_right hs.1]
  let g : ℝ → ℝ := f ∘ c
  have hg : Continuous g := hf.comp_continuous hc hcm
  have hs : Tendsto (fun k => Function.support (ρ k)) atTop (𝓝 (0 : ℝ)).smallSets := by
    rw [tendsto_smallSets_iff]
    intro V hV
    obtain ⟨δ,hδ,hδV⟩ := Metric.mem_nhds_iff.mp hV
    filter_upwards [hε.eventually (gt_mem_nhds hδ)] with k hk s hks
    apply hδV
    have hp := hsupp k (subset_tsupport (ρ k) hks)
    rw [Metric.mem_ball,Real.dist_eq,sub_zero,abs_of_pos hp.1]
    exact hp.2.trans hk
  have ht := convolution_tendsto_right (μ := (volume : Measure ℝ))
    (g := fun _ : ℕ => g) (k := fun _ => b)
    (Eventually.of_forall hρ0) (Eventually.of_forall hρ1) hs
    (Eventually.of_forall fun _ => hg.aestronglyMeasurable)
    (hg.continuousAt.tendsto.comp tendsto_snd) tendsto_const_nhds
  have heq k : (ρ k ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] g) b =
      ∫ s in Set.Ioo a b, ρ k (b-s) * f s := by
    rw [convolution_def]
    simp only [ContinuousLinearMap.lsmul_apply,smul_eq_mul]
    calc
      _ = ∫ s, ρ k (b-s) * g s := by
        have he := integral_sub_left_eq_self (fun s => ρ k s * g (b-s)) volume b
        simpa only [sub_sub_cancel] using he.symm
      _ = ∫ s in Set.Ioo a b, ρ k (b-s) * g s := by
        symm
        apply setIntegral_eq_integral_of_forall_compl_eq_zero
        intro s hs
        have hts := tsupport_time_kernel_subset (hsupp k)
          (show a+ε k ≤ b by linarith [hεb k]) (le_refl b)
        have hz : ρ k (b-s) = 0 := by
          by_contra hz
          exact hs (hts (subset_tsupport (fun s => ρ k (b-s)) hz))
        rw [hz,zero_mul]
      _ = _ := by
        apply setIntegral_congr_fun measurableSet_Ioo
        intro s hs
        simp only [g,Function.comp_apply,hceq ⟨hs.1.le,hs.2.le⟩]
  simpa only [heq,g,Function.comp_apply,hceq ⟨hab.le,le_refl b⟩] using ht

end EinsteinRelation.Correctors
