import EinsteinFull.Calculus.SbxAEndpointJointMeasurabilityR04
import EinsteinFull.Calculus.SbxADenseActionExtensionR04
import EinsteinFull.Calculus.SbxAEndpointL2BoundR04
import Mathlib.MeasureTheory.Function.ContinuousMapDense

/-! Continuity of actual GMP endpoint actions. -/

open EinsteinRelation MeasureTheory ProbabilityTheory Filter Topology
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

noncomputable section
namespace EinsteinFull

/-- Bounded continuous observations of any Markov path kernel have a continuous
annealed endpoint action in L¹. -/
theorem s7_markov_bounded_endpoint_l1_continuous
    {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (f : BoundedContinuousFunction (FieldPair d) ℂ) (s : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => ∫ ω, ‖(∫ γ : Path d,
      f (translate (γ t) (reduce ω)) ∂K ω) -
      (∫ γ : Path d, f (translate (γ s) (reduce ω)) ∂K ω)‖ ∂Q.measure)
      (𝓝 s) (𝓝 0) := by
  let : IsProbabilityMeasure Q.measure := Q.probability
  let M : ℝ≥0 → FieldPair d → ℂ := fun t ω =>
    ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂K ω
  have hc (ω : FieldPair d) : Continuous (fun t => M t ω) := by
    apply continuous_iff_continuousAt.mpr
    intro u
    exact tendsto_integral_filter_of_dominated_convergence (μ := K ω)
      (fun _ : Path d => ‖f‖)
      (Filter.Eventually.of_forall fun t : ℝ≥0 =>
        (f.continuous.comp (Probability.continuous_translate.comp
          ((continuous_eval_const t).prodMk (continuous_const (y := reduce ω))))).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun t : ℝ≥0 =>
        Filter.Eventually.of_forall fun γ : Path d => f.norm_coe_le_norm _)
      (integrable_const ‖f‖)
      (Filter.Eventually.of_forall fun γ : Path d =>
        (f.continuous.comp (Probability.continuous_translate.comp
          (γ.continuous.prodMk (continuous_const (y := reduce ω))))).tendsto u)
  have hb (t : ℝ≥0) (ω : FieldPair d) : ‖M t ω‖ ≤ ‖f‖ := by
    simpa only [measureReal_def, measure_univ, ENNReal.toReal_one, mul_one] using
      (norm_integral_le_of_norm_le_const (μ := K ω)
        (Filter.Eventually.of_forall fun γ : Path d => f.norm_coe_le_norm _))
  have hm (t : ℝ≥0) : StronglyMeasurable (M t) := by
    have hE : Measurable (fun z : FieldPair d × Path d =>
        translate (z.2 t) (reduce z.1)) :=
      (Probability.continuous_translate.comp
        ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
          (Probability.continuous_reduce.comp continuous_fst))).measurable
    exact (f.continuous.stronglyMeasurable.comp_measurable hE).integral_kernel_prod_right'
  have ht := tendsto_integral_filter_of_dominated_convergence (μ := Q.measure)
    (fun _ : FieldPair d => 2 * ‖f‖)
    (Filter.Eventually.of_forall fun t : ℝ≥0 =>
      (((hm t).sub (hm s)).norm).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun t : ℝ≥0 => Filter.Eventually.of_forall fun ω => by
      rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
      exact (norm_sub_le _ _).trans ((add_le_add (hb t ω) (hb s ω)).trans_eq (two_mul ‖f‖).symm))
    (integrable_const (2 * ‖f‖))
    (Filter.Eventually.of_forall fun ω => by
      have h := (((hc ω).sub (continuous_const (y := M s ω))).norm).tendsto s
      change Tendsto (fun t : ℝ≥0 => ‖M t ω - M s ω‖) (𝓝 s)
        (𝓝 (‖M s ω - M s ω‖)) at h
      simpa only [Pi.sub_apply, sub_self, norm_zero] using h)
  simpa only [Pi.sub_apply, sub_self, norm_zero, integral_zero] using ht

/-- The bounded continuous case for the actual supplied forced GMP laws. -/
theorem s7_gmp_bounded_endpoint_l1_continuous
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (f : BoundedContinuousFunction (FieldPair d) ℂ) (s : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => ∫ ω, ‖(∫ γ : Path d,
      f (translate (γ t) (reduce ω)) ∂P (0, ω)) -
      (∫ γ : Path d, f (translate (γ s) (reduce ω)) ∂P (0, ω))‖ ∂Q.measure)
      (𝓝 s) (𝓝 0) := by
  obtain ⟨K, hmark, hK⟩ := s5_gmp_origin_markov_version hd Q mu h0 h1 P hP
  let : IsMarkovKernel K := hmark
  apply (s7_markov_bounded_endpoint_l1_continuous Q K f s).congr
  intro t
  apply integral_congr_ae
  filter_upwards [hK] with ω hω
  rw [hω]

/-- A locally uniform Lipschitz bound extends time continuity from a dense set. -/
theorem s7_orbit_continuous_of_dense_lipschitz
    {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]
    (A : ℝ≥0 → X → Y) (D : Set X) (hD : Dense D)
    (hdense : ∀ x ∈ D, Continuous (fun t => A t x))
    (hbound : ∀ s : ℝ≥0, ∃ B : ℝ, 0 < B ∧
      (∀ᶠ t in 𝓝 s, ∀ x y, dist (A t x) (A t y) ≤ B * dist x y) ∧
      ∀ x y, dist (A s x) (A s y) ≤ B * dist x y)
    (x : X) : Continuous (fun t => A t x) := by
  apply continuous_iff_continuousAt.mpr
  intro s
  obtain ⟨B, hB, hlocal, hs⟩ := hbound s
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨y, hy, hxy⟩ := hD.exists_dist_lt x (div_pos hε (by positivity : 0 < 3 * B))
  have hsmall : B * dist x y < ε / 3 := by
    have h := (lt_div_iff₀ (by positivity : 0 < 3 * B)).mp hxy
    nlinarith
  have hyc := Metric.tendsto_nhds.mp ((hdense y hy).continuousAt (x := s)) (ε / 3) (by positivity)
  filter_upwards [hlocal, hyc] with t ht hty
  have hfirst := ht x y
  have hlast : dist (A s y) (A s x) ≤ B * dist x y := by
    rw [dist_comm]
    exact hs x y
  calc
    dist (A t x) (A s x) ≤ dist (A t x) (A t y) +
        (dist (A t y) (A s y) + dist (A s y) (A s x)) :=
      (dist_triangle (A t x) (A t y) (A s x)).trans
        (add_le_add le_rfl (dist_triangle (A t y) (A s y) (A s x)))
    _ < ε := by linarith

/-- Any L¹-valued family with the actual GMP representative is continuous on
bounded continuous observations. -/
theorem s7_gmp_bounded_operator_orbit_of_rep
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (A : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) → Lp ℂ 1 Q.measure)
    (hrep : ∀ t f, A t f =ᵐ[Q.measure] fun ω => ∫ γ : Path d,
      f (translate (γ t) (reduce ω)) ∂P (0, ω))
    (g : BoundedContinuousFunction (FieldPair d) ℂ) :
    Continuous (fun t => A t (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ g)) := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let F := BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ g
  let M := fun (t : ℝ≥0) (ω : FieldPair d) =>
    ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂P (0, ω)
  have he (t : ℝ≥0) : A t F =ᵐ[Q.measure] M t := by
    have heq := SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q mu h0 h1 P hP t
      (Lp.stronglyMeasurable F).measurable g.continuous.measurable
      (BoundedContinuousFunction.coeFn_toLp 2 (reducedLaw Q) ℂ g)
    filter_upwards [hrep t F, heq] with ω hω hωeq
    exact hω.trans (integral_congr_ae hωeq)
  have hi (t : ℝ≥0) : Integrable (M t) Q.measure :=
    (MeasureTheory.L1.integrable_coeFn (A t F)).congr (he t)
  apply continuous_iff_continuousAt.mpr
  intro s
  rw [ContinuousAt, tendsto_iff_dist_tendsto_zero]
  simp only [dist_eq_norm]
  apply (s7_gmp_bounded_endpoint_l1_continuous hd Q mu h0 h1 P hP g s).congr
  intro t
  symm
  change ‖A t F - A s F‖ = ∫ ω, ‖M t ω - M s ω‖ ∂Q.measure
  rw [MeasureTheory.L1.norm_sub_eq_lintegral]
  change (∫⁻ ω, ‖((fun ω => A t F ω - A s F ω) ω)‖ₑ ∂Q.measure).toReal = _
  have hm : AEStronglyMeasurable (fun ω => A t F ω - A s F ω) Q.measure := by
    apply ((hi t).sub (hi s)).aestronglyMeasurable.congr
    filter_upwards [he t, he s] with ω ht hs
    change M t ω - M s ω = A t F ω - A s F ω
    rw [ht, hs]
  rw [← integral_norm_eq_lintegral_enorm hm]
  apply integral_congr_ae
  filter_upwards [he t, he s] with ω ht hs
  simp only [Pi.sub_apply, ht, hs]

/-- The actual GMP endpoint expectation is integrable in the environment. -/
theorem s7_gmp_endpoint_operator_integrable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    Integrable (fun ω => ∫ γ : Path d,
      f (translate (γ t) (reduce ω)) ∂P (0, ω)) Q.measure := by
  obtain ⟨P₀, hP₀⟩ := SbxS3Section3R01.joint_reduced_kernel_exists hd Q 0
    (by norm_num) (by norm_num)
  obtain ⟨K, hmark, hK⟩ := s5_gmp_origin_markov_version hd Q 0
    (by norm_num) (by norm_num) P₀ hP₀
  letI : IsMarkovKernel K := hmark
  refine ⟨s5_gmp_endpoint_aestronglyMeasurable hd Q mu h0 h1 P hP t f, ?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  apply lt_of_le_of_lt (s9_gmp_endpoint_annealed_horizon_bound hd Q mu h0 h1 P₀ P hP₀ hP K hK t t le_rfl f)
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
    (Lp.eLpNorm_lt_top f)

/-- The actual GMP endpoint action is linear from L² into L¹. -/
def s7GMPEndpointActionLinear
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) :
    Lp ℂ 2 (reducedLaw Q) →ₗ[ℂ] Lp ℂ 1 Q.measure where
  toFun f := (memLp_one_iff_integrable.mpr
    (s7_gmp_endpoint_operator_integrable hd Q mu h0 h1 P hP t f)).toLp
      (fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω))
  map_add' f g := by
    have he := SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q mu h0 h1 P hP t
      (Lp.stronglyMeasurable (f + g)).measurable
      ((Lp.stronglyMeasurable f).measurable.add (Lp.stronglyMeasurable g).measurable)
      (Lp.coeFn_add f g)
    apply Lp.ext
    filter_upwards [he,
      s9_gmp_endpoint_integrable hd Q mu h0 h1 P hP t f,
      s9_gmp_endpoint_integrable hd Q mu h0 h1 P hP t g,
      (memLp_one_iff_integrable.mpr (s7_gmp_endpoint_operator_integrable hd Q mu h0 h1 P hP t (f + g))).coeFn_toLp,
      (memLp_one_iff_integrable.mpr (s7_gmp_endpoint_operator_integrable hd Q mu h0 h1 P hP t f)).coeFn_toLp,
      (memLp_one_iff_integrable.mpr (s7_gmp_endpoint_operator_integrable hd Q mu h0 h1 P hP t g)).coeFn_toLp,
      Lp.coeFn_add
        ((memLp_one_iff_integrable.mpr (s7_gmp_endpoint_operator_integrable hd Q mu h0 h1 P hP t f)).toLp _)
        ((memLp_one_iff_integrable.mpr (s7_gmp_endpoint_operator_integrable hd Q mu h0 h1 P hP t g)).toLp _)]
      with ω he hf hg hfg hf' hg' hadd
    rw [hfg, hadd]
    simp only [Pi.add_apply]
    rw [hf', hg', integral_congr_ae he]
    simpa only [Pi.add_apply] using integral_add hf hg
  map_smul' c f := by
    have he := SbxS4Dynkin.ae_eq_at_supplied_endpoint hd Q mu h0 h1 P hP t
      (Lp.stronglyMeasurable (c • f)).measurable
      ((Lp.stronglyMeasurable f).measurable.const_smul c) (Lp.coeFn_smul c f)
    apply Lp.ext
    filter_upwards [he,
      (memLp_one_iff_integrable.mpr (s7_gmp_endpoint_operator_integrable hd Q mu h0 h1 P hP t (c • f))).coeFn_toLp,
      (memLp_one_iff_integrable.mpr (s7_gmp_endpoint_operator_integrable hd Q mu h0 h1 P hP t f)).coeFn_toLp,
      Lp.coeFn_smul c
        ((memLp_one_iff_integrable.mpr (s7_gmp_endpoint_operator_integrable hd Q mu h0 h1 P hP t f)).toLp _)]
      with ω he hcf hf hsmul
    simp only [RingHom.id_apply]
    rw [hcf, hsmul]
    simp only [Pi.smul_apply]
    rw [hf, integral_congr_ae he]
    simpa only [Pi.smul_apply] using integral_smul c (fun γ : Path d => f (translate (γ t) (reduce ω)))


/-- The actual GMP endpoint action, as a bounded L²-to-L¹ operator. -/
def s7GMPEndpointAction
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 1 Q.measure :=
  (s7GMPEndpointActionLinear hd Q mu h0 h1 P hP t).mkContinuous
    ((ENNReal.ofReal (Real.exp ((Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
      (1 / 2 : ℝ)).toReal) (by
      intro f
      obtain ⟨P₀, hP₀⟩ := SbxS3Section3R01.joint_reduced_kernel_exists hd Q 0
        (by norm_num) (by norm_num)
      obtain ⟨K, hmark, hK⟩ := s5_gmp_origin_markov_version hd Q 0
        (by norm_num) (by norm_num) P₀ hP₀
      letI : IsMarkovKernel K := hmark
      let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp
        ((Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ)
      let A : FieldPair d → ℂ := fun ω =>
        ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)
      have hi : Integrable A Q.measure := s7_gmp_endpoint_operator_integrable hd Q mu h0 h1 P hP t f
      have hb := s9_gmp_endpoint_annealed_horizon_bound hd Q mu h0 h1 P₀ P hP₀ hP K hK t t le_rfl f
      change (∫⁻ ω, ‖A ω‖ₑ ∂Q.measure) ≤ B * eLpNorm f 2 (reducedLaw Q) at hb
      have hfin : B * eLpNorm f 2 (reducedLaw Q) ≠ ∞ :=
        ENNReal.mul_ne_top
          (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne).ne
          (Lp.eLpNorm_ne_top f)
      have hr := ENNReal.toReal_mono hfin hb
      rw [← eLpNorm_one_eq_lintegral_enorm hi.1, ← Lp.norm_toLp A
        (memLp_one_iff_integrable.mpr hi), ENNReal.toReal_mul, ← Lp.norm_def] at hr
      exact hr)

/-- Its representative is the literal actual GMP endpoint expectation. -/
theorem s7_gmp_endpoint_operator_rep
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    s7GMPEndpointAction hd Q mu h0 h1 P hP t f =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω) := by
  exact (memLp_one_iff_integrable.mpr
    (s7_gmp_endpoint_operator_integrable hd Q mu h0 h1 P hP t f)).coeFn_toLp

/-- A single structural bound controls the operators over a finite horizon. -/
theorem s7_gmp_endpoint_operator_opNorm_horizon
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t T : ℝ≥0) (ht : t ≤ T) :
    ‖s7GMPEndpointAction hd Q mu h0 h1 P hP t‖ ≤
      (ENNReal.ofReal (Real.exp ((Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
        (1 / 2 : ℝ)).toReal := by
  have hnorm : ‖s7GMPEndpointAction hd Q mu h0 h1 P hP t‖ ≤
      (ENNReal.ofReal (Real.exp ((Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
        (1 / 2 : ℝ)).toReal := by
    unfold s7GMPEndpointAction
    exact LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _
  refine hnorm.trans (ENNReal.toReal_mono ?_ ?_)
  · exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne).ne
  · apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ (T : ℝ) from ht)
    exact mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)


/-- The actual forced GMP endpoint operator has continuous L¹ orbits for all
complex reduced-law L² data. -/
theorem s7_gmp_endpoint_operator_orbit_continuous
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t : ℝ≥0 => s7GMPEndpointAction hd Q mu h0 h1 P hP t f) := by
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let _ : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  let _ : PolishSpace (FieldPair d) := inferInstance
  let A := fun t : ℝ≥0 => s7GMPEndpointAction hd Q mu h0 h1 P hP t
  let D : Set (Lp ℂ 2 (reducedLaw Q)) := Set.range
    (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ)
  have hD : Dense D := BoundedContinuousFunction.toLp_denseRange ℂ (reducedLaw Q) ℂ (by norm_num)
  have hdense : ∀ G ∈ D, Continuous (fun t => A t G) := by
    rintro G ⟨g, rfl⟩
    exact s7_gmp_bounded_operator_orbit_of_rep hd Q mu h0 h1 P hP
      (fun t x => A t x) (s7_gmp_endpoint_operator_rep hd Q mu h0 h1 P hP) g
  apply s7_orbit_continuous_of_dense_lipschitz (fun t x => A t x) D hD hdense
  intro s
  let C : ℝ := (ENNReal.ofReal (Real.exp
    ((Real.exp (2 * Λ) * Λ) * ((s + 1 : ℝ≥0) : ℝ))) ^ (1 / 2 : ℝ)).toReal
  let B : ℝ := max 1 C
  have hB : 0 < B := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hs : ‖A s‖ ≤ B :=
    (s7_gmp_endpoint_operator_opNorm_horizon hd Q mu h0 h1 P hP s (s + 1)
      (le_add_of_nonneg_right (by positivity))).trans (le_max_right _ _)
  have hlocal : ∀ᶠ t in 𝓝 s, ‖A t‖ ≤ B := by
    filter_upwards [Iio_mem_nhds (show s < s + 1 by simp)] with t ht
    exact (s7_gmp_endpoint_operator_opNorm_horizon hd Q mu h0 h1 P hP t (s + 1) ht.le).trans
      (le_max_right _ _)
  refine ⟨B, hB, ?_, ?_⟩
  · filter_upwards [hlocal] with t ht x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((A t).le_opNorm _).trans (mul_le_mul_of_nonneg_right ht (norm_nonneg _))
  · intro x y
    rw [dist_eq_norm, dist_eq_norm, ← map_sub]
    exact ((A s).le_opNorm _).trans (mul_le_mul_of_nonneg_right hs (norm_nonneg _))

/-- Literal annealed L¹ distance between actual endpoint expectations tends to
zero at every nonnegative time, including zero. -/
theorem s7_gmp_endpoint_l1_norm_tendsto_zero
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (f : Lp ℂ 2 (reducedLaw Q)) (s : ℝ≥0) :
    Tendsto (fun t : ℝ≥0 => ∫ ω, ‖(∫ γ : Path d,
      f (translate (γ t) (reduce ω)) ∂P (0, ω)) -
      (∫ γ : Path d, f (translate (γ s) (reduce ω)) ∂P (0, ω))‖ ∂Q.measure)
      (𝓝 s) (𝓝 0) := by
  let A := fun t : ℝ≥0 => s7GMPEndpointAction hd Q mu h0 h1 P hP t f
  let M := fun (t : ℝ≥0) (ω : FieldPair d) =>
    ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)
  have he (t : ℝ≥0) : A t =ᵐ[Q.measure] M t :=
    s7_gmp_endpoint_operator_rep hd Q mu h0 h1 P hP t f
  have hi (t : ℝ≥0) : Integrable (M t) Q.measure :=
    (MeasureTheory.L1.integrable_coeFn (A t)).congr (he t)
  have hlim : Tendsto (fun t : ℝ≥0 => ‖A t - A s‖) (𝓝 s) (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mp
      ((s7_gmp_endpoint_operator_orbit_continuous hd Q mu h0 h1 P hP f).tendsto s)
  apply hlim.congr
  intro t
  change ‖A t - A s‖ = ∫ ω, ‖M t ω - M s ω‖ ∂Q.measure
  rw [MeasureTheory.L1.norm_sub_eq_lintegral]
  change (∫⁻ ω, ‖((fun ω => A t ω - A s ω) ω)‖ₑ ∂Q.measure).toReal = _
  have hm : AEStronglyMeasurable (fun ω => A t ω - A s ω) Q.measure := by
    apply ((hi t).sub (hi s)).aestronglyMeasurable.congr
    filter_upwards [he t, he s] with ω ht hs
    change M t ω - M s ω = A t ω - A s ω
    rw [ht, hs]
  rw [← integral_norm_eq_lintegral_enorm hm]
  apply integral_congr_ae
  filter_upwards [he t, he s] with ω ht hs
  simp only [Pi.sub_apply, ht, hs]

end EinsteinFull
