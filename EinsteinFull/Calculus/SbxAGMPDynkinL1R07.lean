import EinsteinFull.Calculus.SbxAGMPGraphDynkinR04
import EinsteinFull.Calculus.SbxAEndpointJointMeasurabilityR04
import EinsteinFull.Calculus.SbxAGMPEndpointL1ContinuityR07

/-! Complex L¹ endpoint actions for actual GMP laws. -/

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull

/-- The actual quenched endpoint average. -/
def s13Endpoint {d : ℕ} (P : QuenchedPathLaws d)
    (t : ℝ≥0) (f : FieldPair d → ℂ) (ω : FieldPair d) : ℂ :=
  ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)

/-- The actual endpoint average is integrable over the environment law. -/
theorem s13_gmp_endpoint_integrable_environment
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (s13Endpoint P t f) Q.measure := by
  obtain ⟨H, hH, heq⟩ := s7_gmp_endpoint_L2_jointly_strongly_measurable
    hd Q mu h0 h1 P hP f
  have hm : AEStronglyMeasurable (s13Endpoint P t f) Q.measure := by
    apply ((hH.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable).congr
    filter_upwards [heq] with ω hω
    simpa [s13Endpoint] using hω (t : ℝ)
  obtain ⟨P₀, hP₀⟩ := SbxS3Section3R01.joint_reduced_kernel_exists hd Q 0
    (by norm_num) (by norm_num)
  obtain ⟨K, hmark, hK⟩ := s5_gmp_origin_markov_version hd Q 0
    (by norm_num) (by norm_num) P₀ hP₀
  letI : IsMarkovKernel K := hmark
  have hb := s9_gmp_endpoint_annealed_horizon_bound hd Q mu h0 h1 P₀ P hP₀ hP
    K hK t t le_rfl f
  refine ⟨hm, hasFiniteIntegral_iff_enorm.mpr ?_⟩
  apply lt_of_le_of_lt hb
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
    (Lp.eLpNorm_ne_top f |> lt_top_iff_ne_top.mpr)

/-- The L¹ class of the actual endpoint action. -/
def s13GmpEndpointL1
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) : Lp ℂ 1 Q.measure :=
  (s13_gmp_endpoint_integrable_environment hd Q mu h0 h1 P hP t f).toL1 _

/-- The L¹ class represents the literal endpoint average. -/
theorem s13_gmp_endpoint_L1_rep
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    s13GmpEndpointL1 hd Q mu h0 h1 P hP t f =ᵐ[Q.measure] s13Endpoint P t f :=
  (s13_gmp_endpoint_integrable_environment hd Q mu h0 h1 P hP t f).coeFn_toL1

/-- A jointly measurable endpoint representative is integrable on each finite
 time-environment product, with no additional analytic assumptions. -/
theorem s13_gmp_endpoint_joint_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ H : ℝ × FieldPair d → ℂ,
      Integrable H ((volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))).prod Q.measure) ∧
      ∀ᵐ ω ∂Q.measure, ∀ t : ℝ, H (t, ω) = s13Endpoint P t.toNNReal f ω := by
  obtain ⟨H, hH, heq⟩ := s7_gmp_endpoint_L2_jointly_strongly_measurable
    hd Q mu h0 h1 P hP f
  refine ⟨H, ?_, ?_⟩
  · refine ⟨hH.aestronglyMeasurable, hasFiniteIntegral_iff_enorm.mpr ?_⟩
    rw [lintegral_prod _ hH.enorm.aemeasurable]
    obtain ⟨P₀, hP₀⟩ := SbxS3Section3R01.joint_reduced_kernel_exists hd Q 0
      (by norm_num) (by norm_num)
    obtain ⟨K, hmark, hK⟩ := s5_gmp_origin_markov_version hd Q 0
      (by norm_num) (by norm_num) P₀ hP₀
    letI : IsMarkovKernel K := hmark
    let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
      (1 / 2 : ℝ) * eLpNorm (fun ρ => f ρ) 2 (reducedLaw Q)
    have hbound : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))),
        (∫⁻ ω, ‖H (t, ω)‖ₑ ∂Q.measure) ≤ C := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
      have he : (∫⁻ ω, ‖H (t, ω)‖ₑ ∂Q.measure) =
          ∫⁻ ω, ‖s13Endpoint P t.toNNReal f ω‖ₑ ∂Q.measure := by
        apply lintegral_congr_ae
        filter_upwards [heq] with ω hω
        rw [hω t]
        rfl
      rw [he]
      exact s9_gmp_endpoint_annealed_horizon_bound hd Q mu h0 h1 P₀ P hP₀ hP
        K hK t.toNNReal T (Real.toNNReal_le_iff_le_coe.mpr ht.2) f
    refine lt_of_le_of_lt (lintegral_mono_ae hbound) ?_
    rw [lintegral_const, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top
      (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
      (lt_top_iff_ne_top.mpr (Lp.eLpNorm_ne_top f))) measure_Ioc_lt_top
  · filter_upwards [heq] with ω hω t
    exact hω t

/-- The scalar Dynkin identities combine into the complex identity for the
actual endpoint, with the time integral interpreted in ℂ. -/
theorem s13_gmp_complex_endpoint_dynkin
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g) :
    ∀ᵐ ω ∂Q.measure,
      s13Endpoint P T f ω - f (reduce ω) =
        ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), s13Endpoint P t.toNNReal g ω := by
  obtain ⟨H, hH, heq⟩ := s13_gmp_endpoint_joint_integrable hd Q mu h0 h1 P hP T g
  have hn := s5_gmp_occupation_fubini_of_l2_estimate hd Q mu h0 h1 P hP T
    (s5_gmp_literal_occupation_l2_estimate hd Q mu h0 h1 P hP T)
    (fun ρ => ‖g ρ‖) (Lp.stronglyMeasurable g).measurable.norm (Lp.memLp g).norm
  filter_upwards [s5_gmp_generator_pair_dynkin hd Q mu h0 h1 P hP T f g hfg Complex.reCLM,
    s5_gmp_generator_pair_dynkin hd Q mu h0 h1 P hP T f g hfg Complex.imCLM,
    s9_gmp_endpoint_integrable hd Q mu h0 h1 P hP T f, hn, heq, hH.prod_left_ae, hP]
    with ω hre him hf hn heq htime hω
  obtain ⟨_, R, hR⟩ := hω
  letI : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  letI : IsProbabilityMeasure (P (0, ω)) := by rw [hR 0]; infer_instance
  have hgprod : Integrable (fun p : Path d × ℝ =>
      g (translate (p.1 p.2.toNNReal) (reduce ω)))
      ((P (0, ω)).prod (volume.restrict (Set.Ioc 0 (T : ℝ)))) := by
    apply hn.1.mono'
    · apply StronglyMeasurable.aestronglyMeasurable
      apply (Lp.stronglyMeasurable g).comp_measurable
      exact (Probability.continuous_translate.comp
        ((continuous_eval.comp (continuous_fst.prodMk
          (continuous_real_toNNReal.comp continuous_snd))).prodMk continuous_const)).measurable
    · filter_upwards [] with p
      simp only [Real.norm_eq_abs, abs_norm, le_refl]
  have hgi : ∀ᵐ t ∂(volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))),
      Integrable (fun γ : Path d => g (translate (γ t.toNNReal) (reduce ω))) (P (0, ω)) :=
    hgprod.prod_left_ae
  have hti : Integrable (fun t : ℝ => s13Endpoint P t.toNNReal g ω)
      (volume.restrict (Set.Ioc 0 (T : ℝ))) := by
    apply htime.congr
    exact Filter.Eventually.of_forall fun t => heq t
  have hscalar (L : ℂ →L[ℝ] ℝ) :
      (∫ t in Set.Ioc (0 : ℝ) (T : ℝ), ∫ γ : Path d,
        L (g (translate (γ t.toNNReal) (reduce ω))) ∂P (0, ω)) =
      L (∫ t in Set.Ioc (0 : ℝ) (T : ℝ), s13Endpoint P t.toNNReal g ω) := by
    rw [← L.integral_comp_comm hti]
    apply integral_congr_ae
    filter_upwards [hgi] with t ht
    exact L.integral_comp_comm ht
  have hr := (Complex.reCLM.integral_comp_comm hf)
  have hi := (Complex.imCLM.integral_comp_comm hf)
  rw [hscalar Complex.reCLM, hr] at hre
  rw [hscalar Complex.imCLM, hi] at him
  apply Complex.ext
  · simpa only [s13Endpoint, Complex.sub_re, Complex.reCLM_apply] using hre
  · simpa only [s13Endpoint, Complex.sub_im, Complex.imCLM_apply] using him

/-- Strong measurability of the L¹ curve suffices for Bochner integrability;
the actual endpoint estimate supplies the finite-horizon norm bound. -/
theorem s13_gmp_endpoint_curve_integrable_of_aestronglyMeasurable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q))
    (hm : AEStronglyMeasurable
      (fun t : ℝ => s13GmpEndpointL1 hd Q mu h0 h1 P hP t.toNNReal f)
      (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) :
    Integrable (fun t : ℝ => s13GmpEndpointL1 hd Q mu h0 h1 P hP t.toNNReal f)
      (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
  obtain ⟨P₀, hP₀⟩ := SbxS3Section3R01.joint_reduced_kernel_exists hd Q 0
    (by norm_num) (by norm_num)
  obtain ⟨K, hmark, hK⟩ := s5_gmp_origin_markov_version hd Q 0
    (by norm_num) (by norm_num) P₀ hP₀
  letI : IsMarkovKernel K := hmark
  let C : ℝ≥0∞ := ENNReal.ofReal (Real.exp ((Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
      (1 / 2 : ℝ) * eLpNorm (fun ρ => f ρ) 2 (reducedLaw Q)
  have hC : C ≠ ∞ := ENNReal.mul_ne_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne).ne
    (Lp.eLpNorm_ne_top f)
  apply Integrable.of_bound hm C.toReal
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  have hb := s9_gmp_endpoint_annealed_horizon_bound hd Q mu h0 h1 P₀ P hP₀ hP
    K hK t.toNNReal T (Real.toNNReal_le_iff_le_coe.mpr ht.2) f
  change (∫⁻ ω, ‖s13Endpoint P t.toNNReal f ω‖ₑ ∂Q.measure) ≤ C at hb
  change ‖(s13_gmp_endpoint_integrable_environment hd Q mu h0 h1 P hP t.toNNReal f).toL1
    (s13Endpoint P t.toNNReal f)‖ ≤ C.toReal
  rw [Integrable.norm_toL1_eq_lintegral_enorm]
  exact ENNReal.toReal_mono hC hb

/-- The actual endpoint L¹ curve is continuous in nonnegative time. -/
theorem s13_gmp_endpoint_curve_continuous
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t : ℝ≥0 => s13GmpEndpointL1 hd Q mu h0 h1 P hP t f) := by
  have heq : (fun t : ℝ≥0 => s13GmpEndpointL1 hd Q mu h0 h1 P hP t f) =
      (fun t : ℝ≥0 => s7GMPEndpointAction hd Q mu h0 h1 P hP t f) := by
    funext t
    apply Lp.ext
    exact (s13_gmp_endpoint_L1_rep hd Q mu h0 h1 P hP t f).trans
      (s7_gmp_endpoint_operator_rep hd Q mu h0 h1 P hP t f).symm
  rw [heq]
  exact s7_gmp_endpoint_operator_orbit_continuous hd Q mu h0 h1 P hP f

/-- The actual endpoint curve is Bochner integrable on finite time intervals. -/
theorem s13_gmp_endpoint_curve_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun t : ℝ => s13GmpEndpointL1 hd Q mu h0 h1 P hP t.toNNReal f)
      (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by
  apply s13_gmp_endpoint_curve_integrable_of_aestronglyMeasurable
  exact ((s13_gmp_endpoint_curve_continuous hd Q mu h0 h1 P hP f).comp
    continuous_real_toNNReal).aestronglyMeasurable

/-- Bochner integration of the L¹ endpoint curve evaluates to the scalar
integral of the actual endpoint on a common conull set. -/
theorem s13_gmp_endpoint_bochner_evaluation
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        s13GmpEndpointL1 hd Q mu h0 h1 P hP t.toNNReal f) =ᵐ[Q.measure]
      fun ω => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), s13Endpoint P t.toNNReal f ω := by
  let ν := volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))
  let A : ℝ → Lp ℂ 1 Q.measure :=
    fun t => s13GmpEndpointL1 hd Q mu h0 h1 P hP t.toNNReal f
  have hA : Integrable A ν := s13_gmp_endpoint_curve_integrable hd Q mu h0 h1 P hP T f
  obtain ⟨H, hH, heq⟩ := s13_gmp_endpoint_joint_integrable hd Q mu h0 h1 P hP T f
  have hrep : (fun ω => ∫ t, H (t, ω) ∂ν) =ᵐ[Q.measure]
      (fun ω => ∫ t, s13Endpoint P t.toNNReal f ω ∂ν) := by
    filter_upwards [heq] with ω hω
    exact integral_congr_ae (Filter.Eventually.of_forall hω)
  have hmain : (∫ t, A t ∂ν) =ᵐ[Q.measure] (fun ω => ∫ t, H (t, ω) ∂ν) := by
    apply Integrable.ae_eq_of_forall_setIntegral_eq _ _ (L1.integrable_coeFn _) hH.integral_prod_right
    intro s hs hfinite
    let R := LpToLpRestrictCLM (FieldPair d) ℂ ℝ Q.measure 1 s
    let L : Lp ℂ 1 Q.measure →L[ℝ] ℂ := L1.integralCLM.comp R
    have hL (v : Lp ℂ 1 Q.measure) : L v = ∫ ω in s, v ω ∂Q.measure := by
      change L1.integralCLM (R v) = _
      rw [← L1.integral_eq, L1.integral_eq_integral]
      exact integral_congr_ae (LpToLpRestrictCLM_coeFn ℝ s v)
    rw [← hL, ← L.integral_comp_comm hA]
    have hH' : Integrable H (ν.prod (Q.measure.restrict s)) :=
      hH.mono_measure (Measure.prod_mono le_rfl Measure.restrict_le_self)
    rw [← integral_integral_swap (show Integrable
      (Function.uncurry (fun t ω => H (t, ω))) (ν.prod (Q.measure.restrict s)) from hH')]
    apply integral_congr_ae
    filter_upwards with t
    rw [hL]
    apply integral_congr_ae
    apply ae_restrict_of_ae
    filter_upwards [s13_gmp_endpoint_L1_rep hd Q mu h0 h1 P hP t.toNNReal f, heq] with ω ha hb
    exact ha.trans (hb t).symm
  exact hmain.trans hrep

/-- The pullback of reduced-law L² data is integrable on the full law. -/
theorem s13_reduced_pullback_integrable
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun ω => f (reduce ω)) Q.measure := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hf : Integrable f (reducedLaw Q) := (Lp.memLp f).integrable (by norm_num)
  apply (integrable_map_measure (Lp.stronglyMeasurable f).aestronglyMeasurable
    Probability.measurable_reduce.aemeasurable).mp
  exact hf

/-- The L¹ Dynkin identity follows from the explicit Bochner evaluation rule
for the endpoint curve. This helper isolates that remaining evaluation rule. -/
theorem s13_gmp_L1_dynkin_of_bochner_evaluation
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g)
    (heval : (∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
        s13GmpEndpointL1 hd Q mu h0 h1 P hP t.toNNReal g) =ᵐ[Q.measure]
      fun ω => ∫ t in Set.Ioc (0 : ℝ) (T : ℝ), s13Endpoint P t.toNNReal g ω) :
    s13GmpEndpointL1 hd Q mu h0 h1 P hP T f -
      (s13_reduced_pullback_integrable Q f).toL1 (fun ω => f (reduce ω)) =
    ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
      s13GmpEndpointL1 hd Q mu h0 h1 P hP t.toNNReal g := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_sub (s13GmpEndpointL1 hd Q mu h0 h1 P hP T f)
      ((s13_reduced_pullback_integrable Q f).toL1 (fun ω => f (reduce ω))),
    s13_gmp_endpoint_L1_rep hd Q mu h0 h1 P hP T f,
    (s13_reduced_pullback_integrable Q f).coeFn_toL1,
    s13_gmp_complex_endpoint_dynkin hd Q mu h0 h1 P hP T f g hfg, heval]
    with ω hsub hend hpull hdyn hevalω
  simpa only [hsub, hend, hpull, hevalω, Pi.sub_apply] using hdyn

/-- The actual complex generator-pair Dynkin formula in L¹ of the environment
law, with the endpoint curve integrated in the Bochner sense. -/
theorem s13_gmp_L1_dynkin
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (T : ℝ≥0) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ (mu : ℂ) f g) :
    s13GmpEndpointL1 hd Q mu h0 h1 P hP T f -
      (s13_reduced_pullback_integrable Q f).toL1 (fun ω => f (reduce ω)) =
    ∫ t in Set.Ioc (0 : ℝ) (T : ℝ),
      s13GmpEndpointL1 hd Q mu h0 h1 P hP t.toNNReal g :=
  s13_gmp_L1_dynkin_of_bochner_evaluation hd Q mu h0 h1 P hP T f g hfg
    (s13_gmp_endpoint_bochner_evaluation hd Q mu h0 h1 P hP T g)

end EinsteinFull
