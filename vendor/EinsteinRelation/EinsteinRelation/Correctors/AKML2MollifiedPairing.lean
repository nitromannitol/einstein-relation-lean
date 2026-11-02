import EinsteinRelation.Correctors.AKMHeatKernelMollifiedPairing
import EinsteinRelation.Correctors.PairedPDEHilbertRegularization

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace EinsteinRelation.Correctors

private def spatialTranslate {d : ℕ} (f : Lp ℝ 2 (volume : Measure (Vec d)))
    (v : Vec d) : Lp ℝ 2 (volume : Measure (Vec d)) :=
  Lp.compMeasurePreserving (fun x => x+v) (measurePreserving_add_right volume v) f

private theorem spatialTranslate_continuous {d : ℕ}
    (f : Lp ℝ 2 (volume : Measure (Vec d))) : Continuous (spatialTranslate f) := by
  let τ : Vec d → C(Vec d, Vec d) := fun v => ⟨fun x => x+v, continuous_id.add continuous_const⟩
  have hτ : Continuous τ := ContinuousMap.continuous_of_continuous_uncurry τ (by
    change Continuous (fun z : Vec d × Vec d => z.2+z.1)
    fun_prop)
  exact (continuous_const : Continuous (fun _ : Vec d => f)).compMeasurePreservingLp
    hτ (fun v => measurePreserving_add_right volume v) (by norm_num)

private theorem spatialTranslate_zero {d : ℕ} (f : Lp ℝ 2 (volume : Measure (Vec d))) :
    spatialTranslate f 0 = f := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_compMeasurePreserving f
    (measurePreserving_add_right (volume : Measure (Vec d)) 0)] with x hx
  simpa only [spatialTranslate, add_zero, Function.comp_def] using hx

private theorem spatial_pairing_integrable {d : ℕ} {f h ρ : Vec d → ℝ}
    (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) (hρ : Integrable ρ volume) :
    Integrable (fun z : Vec d × Vec d => ρ z.1 * (f z.2 * h (z.2-z.1)))
      (volume.prod volume) := by
  have hmp := measurePreserving_prod_sub (volume : Measure (Vec d)) (volume : Measure (Vec d))
  have ha := hρ.norm.mul_prod hf.integrable_sq
  have hb := hmp.integrable_comp_of_integrable (hρ.norm.mul_prod hh.integrable_sq)
  have hm := hρ.aestronglyMeasurable.comp_fst.mul
    (hf.aestronglyMeasurable.comp_snd.mul
      (hh.aestronglyMeasurable.comp_snd.comp_measurePreserving hmp))
  refine ((ha.add hb).div_const 2).mono' hm (Eventually.of_forall fun z => ?_)
  simp only [Real.norm_eq_abs, abs_mul]
  change |ρ z.1| * (|f z.2| * |h (z.2-z.1)|) ≤
    (|ρ z.1| * (f z.2)^2 + |ρ z.1| * (h (z.2-z.1))^2) / 2
  have hs : |f z.2| * |h (z.2-z.1)| ≤ ((f z.2)^2 + (h (z.2-z.1))^2)/2 := by
    nlinarith [sq_nonneg (|f z.2|-|h (z.2-z.1)|),sq_abs (f z.2),sq_abs (h (z.2-z.1))]
  nlinarith [mul_le_mul_of_nonneg_left hs (abs_nonneg (ρ z.1))]

/-- Actual L² pairings converge under spatial mollification.
Source: `paper/main.tex:792`; H¹ energy testing in AKM Lemma 8.2. -/
theorem akm_L2_mollification_pairing_tendsto {d : ℕ} {f h : Vec d → ℝ}
    (hf : MemLp f 2 volume) (hh : MemLp h 2 volume) :
    (∀ n : ℕ, Integrable
      (fun x => f x * (∫ y, h y * (akmTraceBump d n).normed volume (x-y))) volume) ∧
    Tendsto (fun n : ℕ => ∫ x,
      f x * (∫ y, h y * (akmTraceBump d n).normed volume (x-y)))
      atTop (𝓝 (∫ x, f x * h x)) := by
  let ρ : ℕ → Vec d → ℝ := fun n => (akmTraceBump d n).normed volume
  let H := hh.toLp h
  let F := hf.toLp f
  have hc := spatialTranslate_continuous H
  have hρd n : ContDiff ℝ (⊤ : ℕ∞) (ρ n) := (akmTraceBump d n).contDiff_normed
  have hρ n : Integrable (ρ n) volume :=
    (hρd n).continuous.integrable_of_hasCompactSupport
      (akmTraceBump d n).hasCompactSupport_normed
  have hi n := spatial_pairing_integrable hf hh (hρ n)
  have heq (n : ℕ) (x : Vec d) : f x * (∫ y, h y * ρ n (x-y)) =
      ∫ w, ρ n w * (f x * h (x-w)) := by
    rw [← integral_sub_left_eq_self (fun y => h y * ρ n (x-y)) volume x,
      ← integral_const_mul]
    apply integral_congr_ae
    exact Eventually.of_forall fun w => by simp only [sub_sub_cancel]; ring
  have hA n : Integrable (fun w : Vec d => ρ n w • spatialTranslate H (-w)) volume :=
    ((hρd n).continuous.smul (hc.comp continuous_neg)).integrable_of_hasCompactSupport
      (akmTraceBump d n).hasCompactSupport_normed.smul_right
  have hin (w : Vec d) : inner ℝ F (spatialTranslate H (-w)) =
      ∫ x, f x * h (x-w) := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hf.coeFn_toLp, Lp.coeFn_compMeasurePreserving H
      (measurePreserving_add_right (volume : Measure (Vec d)) (-w)),
      (measurePreserving_add_right (volume : Measure (Vec d)) (-w)).quasiMeasurePreserving.ae_eq
        hh.coeFn_toLp] with x hx hxT hxH
    change H (x+-w) = h (x+-w) at hxH
    change spatialTranslate H (-w) x = H (x+-w) at hxT
    simp only [F,hx,hxT,hxH,RCLike.inner_apply,conj_trivial,sub_eq_add_neg,mul_comm]
  have hpair (n : ℕ) : (∫ x, f x * (∫ y, h y * ρ n (x-y))) =
      inner ℝ F (∫ w, ρ n w • spatialTranslate H (-w)) := by
    simp_rw [heq]
    rw [← integral_integral_swap (hi n), ← integral_inner (hA n)]
    apply integral_congr_ae
    filter_upwards with w
    rw [inner_smul_right,hin,integral_const_mul]
  have hsupp : Tendsto (fun n => Function.support (ρ n)) atTop
      (𝓝 (0 : Vec d)).smallSets := by
    rw [tendsto_smallSets_iff]
    intro V hV
    obtain ⟨δ,hδ,hδV⟩ := Metric.mem_nhds_iff.mp hV
    filter_upwards [tendsto_one_div_add_atTop_nhds_zero_nat.eventually (gt_mem_nhds hδ)] with n hn
    intro x hx
    apply hδV
    have hx' : ‖x‖ < 1 / ((n:ℝ)+1) := by
      have ht : x ∈ Function.support ((akmTraceBump d n).normed volume) := hx
      rw [(akmTraceBump d n).support_normed_eq] at ht
      simpa [akmTraceBump,Metric.mem_ball,dist_zero_right] using ht
    simpa only [Metric.mem_ball,dist_zero_right] using hx'.trans hn
  have ht := convolution_tendsto_right (μ := (volume : Measure (Vec d)))
    (g := fun _ : ℕ => spatialTranslate H) (k := fun _ => 0)
    (Eventually.of_forall fun n => (akmTraceBump d n).nonneg_normed)
    (Eventually.of_forall fun n => (akmTraceBump d n).integral_normed) hsupp
    (Eventually.of_forall fun _ => hc.aestronglyMeasurable)
    (hc.continuousAt.tendsto.comp tendsto_snd) tendsto_const_nhds
  have ht' : Tendsto (fun n => ∫ w, ρ n w • spatialTranslate H (-w)) atTop (𝓝 H) := by
    simpa only [convolution_def, ContinuousLinearMap.lsmul_apply,zero_sub,spatialTranslate_zero] using ht
  refine ⟨fun n => ?_, ?_⟩
  · change Integrable (fun x => f x * (∫ y, h y * ρ n (x-y))) volume
    simpa only [heq] using (hi n).integral_prod_right
  · have hp := ((continuous_const : Continuous (fun _ : Lp ℝ 2
        (volume : Measure (Vec d)) => F)).inner (𝕜 := ℝ) continuous_id).continuousAt.tendsto.comp ht'
    have hinner : inner ℝ F H = ∫ x, f x * h x := by
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hf.coeFn_toLp,hh.coeFn_toLp] with x hx hy
      simp only [F,H,hx,hy,RCLike.inner_apply,conj_trivial,mul_comm]
    change Tendsto (fun n => ∫ x, f x * (∫ y, h y * ρ n (x-y)))
      atTop (𝓝 (∫ x, f x * h x))
    simpa only [Function.comp_def,id_eq,hpair,hinner] using hp

end EinsteinRelation.Correctors
