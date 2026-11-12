import EinsteinRelation.Correctors.StochasticLocalGradientTail

/-! # Gradient tails with almost-everywhere time bounds

Source: `paper/main.tex:808–816,851–857`. Spatial energy membership and
the resulting moment estimates may have a time-null exceptional set.
The estimates below preserve the literal time integral.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinRelation.Correctors

/-- An almost-everywhere sectionwise moment bound implies actual product
integrability. Source: `paper/main.tex:808–816`. -/
theorem integrable_prod_of_eLpNorm_bound_ae
    {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (ν : Measure T) [SFinite ν]
    {p : ℝ≥0∞} (hp : 1 ≤ p) {g : Ω × T → ℝ} (hg : Measurable g)
    {B : T → ℝ} (hBi : Integrable B ν) (hB : ∀ᵐ t ∂ν, 0 ≤ B t)
    (hbound : ∀ᵐ t ∂ν,
      eLpNorm (fun ω => g (ω,t)) p μ ≤ ENNReal.ofReal (B t)) :
    Integrable g (μ.prod ν) := by
  have hgi : ∀ᵐ t ∂ν, Integrable (fun ω => g (ω,t)) μ := by
    filter_upwards [hbound] with t ht
    exact (show MemLp (fun ω => g (ω,t)) p μ from
      ⟨(hg.comp measurable_prodMk_right).aestronglyMeasurable,
        ht.trans_lt ENNReal.ofReal_lt_top⟩).integrable hp
  have hnorm : ∀ᵐ t ∂ν, (∫ ω, ‖g (ω,t)‖ ∂μ) ≤ B t := by
    filter_upwards [hgi,hB,hbound] with t hti ht0 ht
    apply (ENNReal.ofReal_le_ofReal_iff ht0).mp
    rw [ofReal_integral_norm_eq_lintegral_enorm hti,
      ← eLpNorm_one_eq_lintegral_enorm]
    exact (eLpNorm_le_eLpNorm_of_exponent_le hp
      (hg.comp measurable_prodMk_right).aestronglyMeasurable).trans ht
  rw [integrable_prod_iff' hg.aestronglyMeasurable]
  refine ⟨hgi, hBi.mono' ?_ ?_⟩
  · exact hg.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
  · filter_upwards [hnorm] with t ht
    rwa [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun _ => norm_nonneg _)]

/-- A power bound outside a time-null set controls the actual scalar
tail and its almost-sure integrability. Source: `paper/main.tex:808–816`. -/
theorem stochastic_power_tail_integrable_and_moment_le_ae
    {Ω : Type*} [MeasurableSpace Ω] (Q : Measure Ω) [IsProbabilityMeasure Q]
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    (f : Ω × ℝ → ℝ) (hf : Measurable f)
    {C α T : ℝ} (hC : 0 < C) (hα : 0 < α) (hT : 0 < T)
    (hdecay : ∀ᵐ t ∂volume.restrict (Ioi T),
      eLpNorm (fun ω => f (ω,t)) p Q ≤ ENNReal.ofReal (C*t^(-1-α))) :
    Integrable f (Q.prod (volume.restrict (Ioi T))) ∧
      (∀ᵐ ω ∂Q, IntegrableOn (fun t => f (ω,t)) (Ioi T)) ∧
      eLpNorm (fun ω => ∫ t in Ioi T, f (ω,t)) p Q ≤
        ENNReal.ofReal ((C/α)*T^(-α)) := by
  let B : ℝ → ℝ := fun t => C * (max t T)^(-1-α)
  have hBm : Measurable B :=
    measurable_const.mul ((measurable_id.max measurable_const).pow_const _)
  have hBpos (t : ℝ) : 0 < B t :=
    mul_pos hC (Real.rpow_pos_of_pos (hT.trans_le (le_max_right _ _)) _)
  have hBeq : B =ᵐ[volume.restrict (Ioi T)] fun t => C*t^(-1-α) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact congrArg (fun z : ℝ => C*z^(-1-α)) (max_eq_left ht.le)
  have hBi : IntegrableOn B (Ioi T) :=
    (flow_tail_integrableOn (C := C) hα hT).congr hBeq.symm
  have hBint : (∫ t in Ioi T, B t) = (C/α)*T^(-α) :=
    (integral_congr_ae hBeq).trans (flow_tail_integral_eq hα hT)
  have hmass : 0 < ∫ t in Ioi T, B t := by
    rw [hBint]
    exact mul_pos (div_pos hC hα) (Real.rpow_pos_of_pos hT _)
  have hbound : ∀ᵐ t ∂volume.restrict (Ioi T),
      eLpNorm (fun ω => f (ω,t)) p Q ≤ ENNReal.ofReal (B t) := by
    filter_upwards [hdecay,hBeq] with t ht heq
    simpa only [heq] using ht
  have hi := integrable_prod_of_eLpNorm_bound_ae
    (volume.restrict (Ioi T)) hp hf hBi (ae_of_all _ fun t => (hBpos t).le) hbound
  refine ⟨hi, hi.prod_right_ae, ?_⟩
  simpa only [hBint] using eLpNorm_vector_integral_le_integral_bound_ae
    Q (volume.restrict (Ioi T)) hp hpt f hf.stronglyMeasurable
    hBm hBi hBpos hmass hbound

/-- Almost-everywhere local RMS decay controls the literal spatial RMS
of the infinite-time gradient remainder. Source: `paper/main.tex:808–816,851–857`. -/
theorem stochastic_local_gradient_tail_moment_le_ae
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X] {d : ℕ}
    (Q : Measure Ω) [IsProbabilityMeasure Q]
    (ν : Measure X) [SigmaFinite ν]
    (G : Ω × (ℝ × X) → EuclideanSpace ℝ (Fin d)) (hG : Measurable G)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞)
    {C α T : ℝ} (hC : 0 < C) (hα : 0 < α) (hT : 0 < T)
    (hsections : ∀ᵐ ω ∂Q, ∀ᵐ t ∂volume.restrict (Ioi T),
      MemLp (fun x => G (ω,(t,x))) 2 ν)
    (hdecay : ∀ᵐ t ∂volume.restrict (Ioi T),
      eLpNorm (fun ω => Real.sqrt (∫ x, ‖G (ω,(t,x))‖^2 ∂ν)) p Q ≤
        ENNReal.ofReal (C*t^(-1-α))) :
    (∀ᵐ ω ∂Q, IntegrableOn
      (fun t => Real.sqrt (∫ x, ‖G (ω,(t,x))‖^2 ∂ν)) (Ioi T)) ∧
    MemLp (fun ω => Real.sqrt (∫ x, ‖∫ t in Ioi T, G (ω,(t,x))‖^2 ∂ν)) p Q ∧
    eLpNorm (fun ω => Real.sqrt (∫ x, ‖∫ t in Ioi T, G (ω,(t,x))‖^2 ∂ν)) p Q ≤
      ENNReal.ofReal ((C/α)*T^(-α)) := by
  let a : Ω × ℝ → ℝ := fun z => Real.sqrt (∫ x, ‖G (z.1,(z.2,x))‖^2 ∂ν)
  have hgm : Measurable (fun z : (Ω × ℝ) × X => G (z.1.1,(z.1.2,z.2))) :=
    hG.comp (measurable_fst.fst.prodMk (measurable_fst.snd.prodMk measurable_snd))
  have ham : Measurable a :=
    ((hgm.norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt
  have htail := stochastic_power_tail_integrable_and_moment_le_ae Q hp hpt a ham
    hC hα hT hdecay
  have hreordered : Measurable (fun z : (Ω × X) × ℝ => G (z.1.1,(z.2,z.1.2))) :=
    hG.comp (measurable_fst.fst.prodMk (measurable_snd.prodMk measurable_fst.snd))
  have hint : Measurable (fun z : Ω × X => ∫ t in Ioi T, G (z.1,(t,z.2))) :=
    hreordered.stronglyMeasurable.integral_prod_right'.measurable
  have hF : Measurable (fun ω => Real.sqrt (∫ x, ‖∫ t in Ioi T, G (ω,(t,x))‖^2 ∂ν)) :=
    ((hint.norm.pow_const 2).stronglyMeasurable.integral_prod_right').measurable.sqrt
  have hpoint : ∀ᵐ ω ∂Q,
      ‖Real.sqrt (∫ x, ‖∫ t in Ioi T, G (ω,(t,x))‖^2 ∂ν)‖ ≤
        ‖∫ t in Ioi T, a (ω,t)‖ := by
    filter_upwards [hsections,htail.2.1] with ω hω hωi
    rw [Real.norm_of_nonneg (Real.sqrt_nonneg _),
      Real.norm_of_nonneg (integral_nonneg (fun t => Real.sqrt_nonneg _))]
    exact spatialL2_tail_integral_le_integral_spatialL2 ν hT
      (fun z => G (ω,z)) (hG.comp (measurable_const.prodMk measurable_id)) hω hωi
  have hnorm := (eLpNorm_mono_ae hpoint).trans htail.2.2
  exact ⟨htail.2.1,⟨hF.aestronglyMeasurable,lt_of_le_of_lt hnorm ENNReal.ofReal_lt_top⟩,hnorm⟩

end EinsteinRelation.Correctors
