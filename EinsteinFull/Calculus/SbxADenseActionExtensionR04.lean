import EinsteinFull.Calculus.SbxAEndpointL2BoundR04
import EinsteinFull.Calculus.ComplexHorizontalDensitySupport
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! Extension of the actual GMP endpoint identity from the horizontal domain. -/

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull

/-- The actual endpoint integral is an almost everywhere strongly measurable function
of the environment. -/
theorem s5_gmp_endpoint_aestronglyMeasurable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    AEStronglyMeasurable (fun ω => ∫ γ : Path d,
      f (translate (γ t) (reduce ω)) ∂P (0, ω)) Q.measure := by
  obtain ⟨K, hmarkov, hK⟩ := s5_gmp_origin_markov_version hd Q mu h0 h1 P hP
  letI : IsMarkovKernel K := hmarkov
  let E : FieldPair d × Path d → FieldPair d := fun z => translate (z.2 t) (reduce z.1)
  have hE : Measurable E := (Probability.continuous_translate.comp
    ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
      (Probability.continuous_reduce.comp continuous_fst))).measurable
  have hm : StronglyMeasurable (fun ω => ∫ γ : Path d, f (E (ω, γ)) ∂K ω) :=
    ((Lp.stronglyMeasurable f).comp_measurable hE).integral_kernel_prod_right'
  apply hm.aestronglyMeasurable.congr
  filter_upwards [hK] with ω hω
  simp only [E, hω]

/-- A GMP endpoint identity on any dense class extends to every complex
reduced-law L² class. -/
theorem s5_gmp_action_of_dense_identity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (D : Set (Lp ℂ 2 (reducedLaw Q))) (hD : Dense D)
    (htest : ∀ f : Lp ℂ 2 (reducedLaw Q), f ∈ D →
      (fun ω => forcedComplexEvolution Q (firstCoordinateIndex hd) (mu : ℂ) t f (reduce ω))
        =ᵐ[Q.measure] fun ω => ∫ γ : Path d,
          f (translate (γ t) (reduce ω)) ∂P (0, ω))
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (P (0, ω)) ∧
      forcedComplexEvolution Q (firstCoordinateIndex hd) (mu : ℂ) t f (reduce ω) =
        ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω) := by
  letI := reducedLaw_probability Q
  obtain ⟨u, hu, huf⟩ := mem_closure_iff_seq_limit.mp (hD f)
  let A (v : Lp ℂ 2 (reducedLaw Q)) (ω : FieldPair d) :=
    ∫ γ : Path d, v (translate (γ t) (reduce ω)) ∂P (0, ω)
  let T := forcedComplexEvolution Q (firstCoordinateIndex hd) (mu : ℂ) t
  have hsub : Tendsto (fun n => ‖u n - f‖) atTop (𝓝 0) := by
    simpa only [sub_self, norm_zero] using (huf.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => f) atTop (𝓝 f))).norm
  have hsubE : Tendsto (fun n => eLpNorm (fun ρ => (u n - f) ρ) 2 (reducedLaw Q))
      atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal hsub
    simpa only [ENNReal.ofReal_zero, Lp.norm_def,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)] using h
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ)
  have hC : C ≠ ∞ := (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne).ne
  have hA : Tendsto (fun n => eLpNorm (A (u n) - A f) 1 Q.measure) atTop (𝓝 0) := by
    have hb (n : ℕ) : eLpNorm (A (u n) - A f) 1 Q.measure ≤
        C * eLpNorm (fun ρ => (u n - f) ρ) 2 (reducedLaw Q) := by
      rw [eLpNorm_one_eq_lintegral_enorm
        ((s5_gmp_endpoint_aestronglyMeasurable hd Q mu h0 h1 P hP t (u n)).sub
          (s5_gmp_endpoint_aestronglyMeasurable hd Q mu h0 h1 P hP t f))]
      exact s9_gmp_endpoint_action_sub_horizon_bound hd Q mu h0 h1 P hP t t le_rfl (u n) f
    have hc : Tendsto (fun n => C * eLpNorm (fun ρ => (u n - f) ρ) 2 (reducedLaw Q))
        atTop (𝓝 0) := by
      simpa only [mul_zero] using ENNReal.Tendsto.const_mul hsubE (Or.inr hC)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hc (fun _ => bot_le) hb
  obtain ⟨ns, hns, ha⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (1 : ℝ≥0∞) ≠ 0) hA).exists_seq_tendsto_ae
  have hTu : Tendsto (fun n => T (u (ns n))) atTop (𝓝 (T f)) :=
    (T.continuous.tendsto f).comp (huf.comp hns.tendsto_atTop)
  have hTE : Tendsto (fun n => eLpNorm (fun ρ => (T (u (ns n)) - T f) ρ) 2
      (reducedLaw Q)) atTop (𝓝 0) := by
    have h := ENNReal.tendsto_ofReal (show Tendsto (fun n => ‖T (u (ns n)) - T f‖)
      atTop (𝓝 0) by simpa only [sub_self, norm_zero] using (hTu.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => T f) atTop (𝓝 (T f)))).norm)
    simpa only [ENNReal.ofReal_zero, Lp.norm_def,
      ENNReal.ofReal_toReal (Lp.eLpNorm_ne_top _)] using h
  have hTE' : Tendsto (fun n => eLpNorm ((fun ρ => T (u (ns n)) ρ) - (fun ρ => T f ρ))
      2 (reducedLaw Q)) atTop (𝓝 0) := by
    apply hTE.congr
    intro n
    exact eLpNorm_congr_ae (Lp.coeFn_sub _ _)
  obtain ⟨ms, hms, ht⟩ :=
    (tendstoInMeasure_of_tendsto_eLpNorm (by norm_num : (2 : ℝ≥0∞) ≠ 0) hTE').exists_seq_tendsto_ae
  have ht' := ae_of_ae_map Probability.measurable_reduce.aemeasurable ht
  filter_upwards [s9_gmp_endpoint_integrable hd Q mu h0 h1 P hP t f,
    ha, ht', ae_all_iff.mpr (fun n => htest (u (ns (ms n))) (hu (ns (ms n))))]
    with ω hi haω htω he
  refine ⟨hi, ?_⟩
  exact tendsto_nhds_unique htω ((haω.comp hms.tendsto_atTop).congr' (Eventually.of_forall fun n => (he n).symm))

/-- The full complex horizontal Sobolev domain is a valid dense test class. -/
theorem s5_gmp_action_of_horizontal_identity
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0)
    (htest : ∀ f : Lp ℂ 2 (reducedLaw Q),
      (∃ G : Fin d → Lp ℂ 2 (reducedLaw Q),
        HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) →
      (fun ω => forcedComplexEvolution Q (firstCoordinateIndex hd) (mu : ℂ) t f (reduce ω))
        =ᵐ[Q.measure] fun ω => ∫ γ : Path d,
          f (translate (γ t) (reduce ω)) ∂P (0, ω))
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (P (0, ω)) ∧
      forcedComplexEvolution Q (firstCoordinateIndex hd) (mu : ℂ) t f (reduce ω) =
        ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω) := by
  letI := reducedLaw_probability Q
  exact s5_gmp_action_of_dense_identity hd Q mu h0 h1 P hP t _
    (dense_complexHorizontalH1 (reducedLaw Q) (reducedLaw_stationary Q)) htest f

/-- A measurable reduced-law representative has the same quenched endpoint
integral and integrability as its L² class. -/
theorem s5_gmp_endpoint_representative_independent
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) (g : FieldPair d → ℂ)
    (hg : Measurable g) (hrep : f =ᵐ[reducedLaw Q] g) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => g (translate (γ t) (reduce ω))) (P (0, ω)) ∧
      (∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) =
        ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂P (0, ω) := by
  filter_upwards [s9_gmp_endpoint_integrable hd Q mu h0 h1 P hP t f,
    SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q mu h0 h1 P hP t
      (Lp.stronglyMeasurable f).measurable hg hrep] with ω hi he
  exact ⟨hi.congr he, integral_congr_ae he⟩

end EinsteinFull
