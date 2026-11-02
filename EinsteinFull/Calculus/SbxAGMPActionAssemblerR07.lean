import EinsteinFull.Calculus.SbxAGMPEndpointL1ContinuityR07
import EinsteinFull.Calculus.SbxAGMPDynkinL1R07
import EinsteinFull.Calculus.SbxAGMPGraphDynkinR04
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import MarkovProcess.Semigroup.Generator

/-! Actual GMP endpoint operators on reduced-law L², valued in annealed L¹. -/
open EinsteinRelation MeasureTheory ProbabilityTheory Filter Set
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull

/-- The actual GMP endpoint expectation is integrable in the environment. -/
theorem s8_gmp_action_integrable
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
  let : IsMarkovKernel K := hmark
  refine ⟨s5_gmp_endpoint_aestronglyMeasurable hd Q mu h0 h1 P hP t f, ?_⟩
  apply hasFiniteIntegral_iff_enorm.mpr
  apply lt_of_le_of_lt (s9_gmp_endpoint_annealed_horizon_bound hd Q mu h0 h1 P₀ P hP₀ hP K hK t t le_rfl f)
  exact ENNReal.mul_lt_top
    (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne)
    (Lp.eLpNorm_lt_top f)

/-- The actual GMP endpoint action is linear from L² into L¹. -/
def s8GMPActionLinear
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) :
    Lp ℂ 2 (reducedLaw Q) →ₗ[ℂ] Lp ℂ 1 Q.measure where
  toFun f := (memLp_one_iff_integrable.mpr
    (s8_gmp_action_integrable hd Q mu h0 h1 P hP t f)).toLp
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
      (memLp_one_iff_integrable.mpr (s8_gmp_action_integrable hd Q mu h0 h1 P hP t (f + g))).coeFn_toLp,
      (memLp_one_iff_integrable.mpr (s8_gmp_action_integrable hd Q mu h0 h1 P hP t f)).coeFn_toLp,
      (memLp_one_iff_integrable.mpr (s8_gmp_action_integrable hd Q mu h0 h1 P hP t g)).coeFn_toLp,
      Lp.coeFn_add
        ((memLp_one_iff_integrable.mpr (s8_gmp_action_integrable hd Q mu h0 h1 P hP t f)).toLp _)
        ((memLp_one_iff_integrable.mpr (s8_gmp_action_integrable hd Q mu h0 h1 P hP t g)).toLp _)]
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
      (memLp_one_iff_integrable.mpr (s8_gmp_action_integrable hd Q mu h0 h1 P hP t (c • f))).coeFn_toLp,
      (memLp_one_iff_integrable.mpr (s8_gmp_action_integrable hd Q mu h0 h1 P hP t f)).coeFn_toLp,
      Lp.coeFn_smul c
        ((memLp_one_iff_integrable.mpr (s8_gmp_action_integrable hd Q mu h0 h1 P hP t f)).toLp _)]
      with ω he hcf hf hsmul
    simp only [RingHom.id_apply]
    rw [hcf, hsmul]
    simp only [Pi.smul_apply]
    rw [hf, integral_congr_ae he]
    simpa only [Pi.smul_apply] using integral_smul c (fun γ : Path d => f (translate (γ t) (reduce ω)))


/-- The actual GMP endpoint action, as a bounded L²-to-L¹ operator. -/
def s8GMPAction
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 1 Q.measure :=
  (s8GMPActionLinear hd Q mu h0 h1 P hP t).mkContinuous
    ((ENNReal.ofReal (Real.exp ((Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
      (1 / 2 : ℝ)).toReal) (by
      intro f
      obtain ⟨P₀, hP₀⟩ := SbxS3Section3R01.joint_reduced_kernel_exists hd Q 0
        (by norm_num) (by norm_num)
      obtain ⟨K, hmark, hK⟩ := s5_gmp_origin_markov_version hd Q 0
        (by norm_num) (by norm_num) P₀ hP₀
      let : IsMarkovKernel K := hmark
      let B : ℝ≥0∞ := ENNReal.ofReal (Real.exp
        ((Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^ (1 / 2 : ℝ)
      let A : FieldPair d → ℂ := fun ω =>
        ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)
      have hi : Integrable A Q.measure := s8_gmp_action_integrable hd Q mu h0 h1 P hP t f
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
theorem s8_gmp_action_rep
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    s8GMPAction hd Q mu h0 h1 P hP t f =ᵐ[Q.measure]
      fun ω => ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω) := by
  exact (memLp_one_iff_integrable.mpr
    (s8_gmp_action_integrable hd Q mu h0 h1 P hP t f)).coeFn_toLp

/-- A single structural bound controls the operators over a finite horizon. -/
theorem s8_gmp_action_opNorm_horizon
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t T : ℝ≥0) (ht : t ≤ T) :
    ‖s8GMPAction hd Q mu h0 h1 P hP t‖ ≤
      (ENNReal.ofReal (Real.exp ((Real.exp (2 * Λ₀) * Λ₀) * (T : ℝ))) ^
        (1 / 2 : ℝ)).toReal := by
  have hnorm : ‖s8GMPAction hd Q mu h0 h1 P hP t‖ ≤
      (ENNReal.ofReal (Real.exp ((Real.exp (2 * Λ₀) * Λ₀) * (t : ℝ))) ^
        (1 / 2 : ℝ)).toReal := by
    unfold s8GMPAction
    exact LinearMap.mkContinuous_norm_le _ ENNReal.toReal_nonneg _
  refine hnorm.trans (ENNReal.toReal_mono ?_ ?_)
  · exact (ENNReal.rpow_lt_top_of_nonneg (by norm_num) ENNReal.ofReal_lt_top.ne).ne
  · apply ENNReal.rpow_le_rpow _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
    apply ENNReal.ofReal_le_ofReal
    apply Real.exp_le_exp.mpr
    apply mul_le_mul_of_nonneg_left (show (t : ℝ) ≤ (T : ℝ) from ht)
    exact mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)


/-- A locally bounded strongly convergent operator family may be applied to
vectors converging at the same time. -/
theorem s8_tendsto_apply_of_eventually_bounded
    {α E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {l : Filter α} (A : α → E →L[ℝ] F) (B : E →L[ℝ] F)
    (u : α → E) (v : E) (C : ℝ) (_hC : 0 ≤ C)
    (hbound : ∀ᶠ x in l, ‖A x‖ ≤ C)
    (hA : Tendsto (fun x => A x v) l (𝓝 (B v)))
    (hu : Tendsto u l (𝓝 v)) :
    Tendsto (fun x => A x (u x)) l (𝓝 (B v)) := by
  have hz : Tendsto (fun x => A x (u x - v)) l (𝓝 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    apply squeeze_zero' (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (hbound.mono fun x hx => (A x).le_opNorm _ |>.trans
        (mul_le_mul_of_nonneg_right hx (norm_nonneg _)))
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_iff_norm_sub_tendsto_zero.mp hu)
  simpa only [map_sub, sub_add_cancel, zero_add] using hz.add hA

/-- Product rule for a strongly continuous operator family, requiring only a
local operator bound and derivatives at the fixed and moving arguments. -/
theorem s8_hasDerivWithinAt_strong_operator_apply
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : ℝ → E →L[ℝ] F) (v : ℝ → E) (s : ℝ) (v' : E) (w : F)
    (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ᶠ y in 𝓝[>] s, ‖A y‖ ≤ C)
    (hcont : Tendsto (fun y => A y v') (𝓝[>] s) (𝓝 (A s v')))
    (hv : HasDerivWithinAt v v' (Ioi s) s)
    (hA : HasDerivWithinAt (fun y => A y (v s)) w (Ioi s) s) :
    HasDerivWithinAt (fun y => A y (v y)) (A s v' + w) (Ioi s) s := by
  apply (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s)).mpr
  have h1 : Tendsto (fun y => A y (slope v s y)) (𝓝[>] s) (𝓝 (A s v')) :=
    s8_tendsto_apply_of_eventually_bounded A (A s) (slope v s) v' C hC
      hbound hcont ((hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s)).mp hv)
  have h2 := (hasDerivWithinAt_iff_tendsto_slope' (lt_irrefl s)).mp hA
  apply (h1.add h2).congr'
  filter_upwards [self_mem_nhdsWithin] with y hy
  simp only [slope_def_module, map_smul, map_sub]
  module


/-- A bounded endpoint-action family satisfying the generator equation agrees
with the semigroup on every generator-domain datum.  No semigroup law is
required of the endpoint action. -/
theorem s8_action_eq_comp_semigroup_of_generator_deriv
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (A : ℝ → E →L[ℝ] F)
    (hcont : ∀ x, Continuous (fun t => A t x))
    (hbound : ∀ T : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ‖A t‖ ≤ C)
    (hderiv : ∀ (x : S.generatorDomain) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (fun s => A s x) (A t (S.generator x)) (Ioi t) t)
    (t : ℝ≥0) (x : S.generatorDomain) : A (t : ℝ) x = A 0 (S t x) := by
  obtain ⟨C, hC, hCbound⟩ := hbound (t : ℝ)
  let v : ℝ → E := fun s => S (Real.toNNReal ((t : ℝ) - s)) x
  let w : ℝ → F := fun s => A s (v s)
  have hvcont : Continuous v :=
    (S.continuous_operator_toNNReal x).comp (continuous_const.sub continuous_id)
  have hwcont : ContinuousOn w (Icc 0 (t : ℝ)) := by
    intro s hs
    apply s8_tendsto_apply_of_eventually_bounded A (A s) v (v s) C hC
    · filter_upwards [self_mem_nhdsWithin] with y hy
      exact hCbound y hy
    · exact ((hcont (v s)).tendsto s).mono_left nhdsWithin_le_nhds
    · exact (hvcont.tendsto s).mono_left nhdsWithin_le_nhds
  have hwderiv : ∀ s ∈ Ico 0 (t : ℝ), HasDerivWithinAt w 0 (Ioi s) s := by
    intro s hs
    have hpos : 0 < (t : ℝ) - s := sub_pos.mpr hs.2
    let r : ℝ≥0 := Real.toNNReal ((t : ℝ) - s)
    have hmem : v s ∈ S.generatorDomain := S.operator_mem_generatorDomain x r
    have hv : HasDerivWithinAt v (-(S r (S.generator x))) (Ioi s) s := by
      have h := (S.hasDerivAt_operator_toNNReal x hpos).scomp s
        ((hasDerivAt_const s (t : ℝ)).sub (hasDerivAt_id s))
      simpa only [v, r, zero_sub, neg_one_smul, Function.comp_def] using h.hasDerivWithinAt
    have ha : HasDerivWithinAt (fun y => A y (v s))
        (A s (S r (S.generator x))) (Ioi s) s := by
      have hgen : S.generator ⟨v s, hmem⟩ = S r (S.generator x) := by
        change S.generator ⟨S r x, _⟩ = _
        exact S.generator_operator x r
      simpa only [hgen] using hderiv ⟨v s, hmem⟩ s hs.1
    have hb : ∀ᶠ y in 𝓝[>] s, ‖A y‖ ≤ C := by
      filter_upwards [Ioo_mem_nhdsGT hs.2] with y hy
      exact hCbound y ⟨hs.1.trans hy.1.le, hy.2.le⟩
    have hc : Tendsto (fun y => A y (-(S r (S.generator x)))) (𝓝[>] s)
        (𝓝 (A s (-(S r (S.generator x))))) :=
      ((hcont (-(S r (S.generator x)))).tendsto s).mono_left nhdsWithin_le_nhds
    have h := s8_hasDerivWithinAt_strong_operator_apply A v s
      (-(S r (S.generator x))) (A s (S r (S.generator x))) C hC hb hc hv ha
    simpa only [w, map_neg, neg_add_cancel] using h
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le t.coe_nonneg
    hwcont (fun s hs => hwderiv s ⟨hs.1.le, hs.2⟩)
    (IntervalIntegrable.zero : IntervalIntegrable (fun _ : ℝ => (0 : F))
      MeasureTheory.volume 0 (t : ℝ))
  simpa only [intervalIntegral.integral_zero, w, v, sub_self, sub_zero,
    Real.toNNReal_zero, S.zero_apply, Real.toNNReal_coe, sub_eq_zero] using he.symm

/-- The generator-domain comparison extends to all initial data by density. -/
theorem s8_action_eq_comp_semigroup
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (A : ℝ → E →L[ℝ] F)
    (hcont : ∀ x, Continuous (fun t => A t x))
    (hbound : ∀ T : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ‖A t‖ ≤ C)
    (hderiv : ∀ (x : S.generatorDomain) (t : ℝ), 0 ≤ t →
      HasDerivWithinAt (fun s => A s x) (A t (S.generator x)) (Ioi t) t)
    (t : ℝ≥0) (x : E) : A (t : ℝ) x = A 0 (S t x) := by
  have heq : (fun x => A (t : ℝ) x) = fun x => A 0 (S t x) := by
    apply Continuous.ext_on S.dense_generatorDomain (A (t : ℝ)).continuous
      ((A 0).continuous.comp (S t).continuous)
    intro x hx
    exact s8_action_eq_comp_semigroup_of_generator_deriv S A hcont hbound hderiv t ⟨x, hx⟩
  exact congrFun heq x

/-- An integrated generator identity gives the same comparison, with no
semigroup law assumed for the action family. -/
theorem s8_action_eq_comp_semigroup_of_integrated_generator
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (A : ℝ → E →L[ℝ] F)
    (hcont : ∀ x, Continuous (fun t => A t x))
    (hbound : ∀ T : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T, ‖A t‖ ≤ C)
    (hdyn : ∀ (x : S.generatorDomain) (t : ℝ), 0 ≤ t →
      A t x - A 0 x = ∫ s in (0 : ℝ)..t, A s (S.generator x))
    (t : ℝ≥0) (x : E) : A (t : ℝ) x = A 0 (S t x) := by
  apply s8_action_eq_comp_semigroup S A hcont hbound _ t x
  intro y t ht
  let u : ℝ → F := fun s => A s (S.generator y)
  have hu : Continuous u := hcont (S.generator y)
  have hd := (intervalIntegral.integral_hasDerivAt_right (hu.intervalIntegrable 0 t)
    hu.stronglyMeasurable.stronglyMeasurableAtFilter hu.continuousAt).add_const (A 0 y)
  have hderiv : HasDerivWithinAt (fun s => A s y) (A t (S.generator y)) (Ici 0) t := by
    apply hd.hasDerivWithinAt.congr_of_mem _ ht
    intro s hs
    exact sub_eq_iff_eq_add.mp (hdyn y s hs)
  exact hderiv.mono (fun s hs => ht.trans hs.le)



/-- The shifted forced evolution, viewed as a real contraction semigroup. -/
def s8ShiftedForcedSemigroup {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ) :
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup
      (Lp ℂ 2 (reducedLaw Q)) where
  operator t := (shiftedForcedComplexEvolution Q i ζ t).restrictScalars ℝ
  operator_zero := by
    apply ContinuousLinearMap.ext
    intro f
    simpa only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.id_apply] using
      congrArg (fun A : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) => A f)
        (shiftedForcedComplexEvolution_zero Q i ζ)
  operator_add s t := by
    apply ContinuousLinearMap.ext
    intro f
    simpa only [ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.comp_apply] using
      congrArg (fun A : Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) => A f)
        (shiftedForcedComplexEvolution_add Q i ζ s t)
  opNorm_le_one t := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro f
    simpa only [one_mul, ContinuousLinearMap.coe_restrictScalars'] using
      norm_shiftedForcedComplexEvolution_apply_le Q i ζ t f
  continuous_orbit f := continuous_shiftedForcedComplexEvolution_apply Q i ζ f

/-- The actual endpoint operator after the standard exponential shift. -/
def s8ShiftedGMPAction {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ) : Lp ℂ 2 (reducedLaw Q) →L[ℝ] Lp ℂ 1 Q.measure :=
  Real.exp (-(complexForceShift d Λ₀ (mu : ℂ)) * t) •
    (s8GMPAction hd Q mu h0 h1 P hP t.toNNReal).restrictScalars ℝ

/-- The shifted actual GMP endpoint operator has continuous L¹ orbits. -/
theorem s8_shifted_gmp_action_continuous {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    Continuous (fun t => s8ShiftedGMPAction hd Q mu h0 h1 P hP t f) := by
  have heq (t : ℝ≥0) : s8GMPAction hd Q mu h0 h1 P hP t f =
      s7GMPEndpointAction hd Q mu h0 h1 P hP t f := by
    apply Lp.ext
    exact (s8_gmp_action_rep hd Q mu h0 h1 P hP t f).trans
      (s7_gmp_endpoint_operator_rep hd Q mu h0 h1 P hP t f).symm
  have horbit : Continuous (fun t : ℝ≥0 => s8GMPAction hd Q mu h0 h1 P hP t f) := by
    apply Continuous.congr (s7_gmp_endpoint_operator_orbit_continuous hd Q mu h0 h1 P hP f)
    intro t
    exact (heq t).symm
  have h := (Real.continuous_exp.comp
    ((continuous_const (y := -(complexForceShift d Λ₀ (mu : ℂ)))).mul continuous_id)).smul
    (horbit.comp continuous_real_toNNReal)
  apply h.congr
  intro t
  rfl

/-- The shifted actual endpoint operators are uniformly bounded on finite horizons. -/
theorem s8_shifted_gmp_action_horizon {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P) :
    ∀ T : ℝ, ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Icc 0 T,
      ‖s8ShiftedGMPAction hd Q mu h0 h1 P hP t‖ ≤ C := by
  intro T
  let C : ℝ := (ENNReal.ofReal (Real.exp
    ((Real.exp (2 * Λ₀) * Λ₀) * (T.toNNReal : ℝ))) ^ (1 / 2 : ℝ)).toReal
  refine ⟨C, ENNReal.toReal_nonneg, ?_⟩
  intro t ht
  have hexp : Real.exp (-(complexForceShift d Λ₀ (mu : ℂ)) * t) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (complexForceShift_nonneg Q _)) ht.1
  have hop := s8_gmp_action_opNorm_horizon hd Q mu h0 h1 P hP t.toNNReal T.toNNReal
      (Real.toNNReal_le_toNNReal ht.2)
  change _ ≤ C at hop
  rw [s8ShiftedGMPAction, norm_smul, Real.norm_eq_abs,
    abs_of_pos (Real.exp_pos _), ContinuousLinearMap.norm_restrictScalars]
  calc
    _ ≤ 1 * C := mul_le_mul hexp hop (norm_nonneg _) zero_le_one
    _ = C := one_mul C

/-- Conditional uniqueness from the integrated shifted graph equation for the actual GMP endpoint operator. -/
theorem s8_shifted_gmp_action_eq_evolution_of_integrated_graph
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (hdyn : ∀ (x : (s8ShiftedForcedSemigroup Q (firstCoordinateIndex hd) (mu : ℂ)).generatorDomain)
      (t : ℝ), 0 ≤ t →
      s8ShiftedGMPAction hd Q mu h0 h1 P hP t x -
          s8ShiftedGMPAction hd Q mu h0 h1 P hP 0 x =
        ∫ s in (0 : ℝ)..t, s8ShiftedGMPAction hd Q mu h0 h1 P hP s
          ((s8ShiftedForcedSemigroup Q (firstCoordinateIndex hd) (mu : ℂ)).generator x))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    s8ShiftedGMPAction hd Q mu h0 h1 P hP t f =
      s8ShiftedGMPAction hd Q mu h0 h1 P hP 0
        (shiftedForcedComplexEvolution Q (firstCoordinateIndex hd) (mu : ℂ) t f) := by
  exact s8_action_eq_comp_semigroup_of_integrated_generator
    (s8ShiftedForcedSemigroup Q (firstCoordinateIndex hd) (mu : ℂ))
    (s8ShiftedGMPAction hd Q mu h0 h1 P hP)
    (s8_shifted_gmp_action_continuous hd Q mu h0 h1 P hP)
    (s8_shifted_gmp_action_horizon hd Q mu h0 h1 P hP) hdyn t f

/-- At time zero the actual GMP endpoint operator pulls back along reduction. -/
theorem s8_gmp_action_zero
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    (s8GMPAction hd Q mu h0 h1 P hP 0 f : FieldPair d → ℂ) =ᵐ[Q.measure]
      fun ω => f (reduce ω) := by
  have hi : firstCoordinateIndex hd = (⟨0, by omega⟩ : Fin d) := Fin.ext rfl
  have hmp : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω mu) 0 (P (0, ω)) := by
    filter_upwards [SbxS4Dynkin.reduced_kernel_solves_martingale_problem hd Q mu h0 h1 P hP] with ω hω
    simpa only [hi] using hω 0
  filter_upwards [s8_gmp_action_rep hd Q mu h0 h1 P hP 0 f,
      c27_real_force_quenched_action_zero_time hd Q mu P hmp f] with ω hr hzero
  rw [hr, ← hzero.2, forcedComplexEvolution_zero, ContinuousLinearMap.id_apply]

/-- The literal GMP endpoint identity follows from the integrated shifted graph equation. -/
theorem s8_gmp_endpoint_eq_evolution_of_integrated_graph
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (hdyn : ∀ (x : (s8ShiftedForcedSemigroup Q (firstCoordinateIndex hd) (mu : ℂ)).generatorDomain)
      (t : ℝ), 0 ≤ t →
      s8ShiftedGMPAction hd Q mu h0 h1 P hP t x -
          s8ShiftedGMPAction hd Q mu h0 h1 P hP 0 x =
        ∫ s in (0 : ℝ)..t, s8ShiftedGMPAction hd Q mu h0 h1 P hP s
          ((s8ShiftedForcedSemigroup Q (firstCoordinateIndex hd) (mu : ℂ)).generator x))
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (P (0, ω)) ∧
      forcedComplexEvolution Q (firstCoordinateIndex hd) (mu : ℂ) t f (reduce ω) =
        ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω) := by
  let c := complexForceShift d Λ₀ (mu : ℂ)
  let g := shiftedForcedComplexEvolution Q (firstCoordinateIndex hd) (mu : ℂ) t f
  let A := s8GMPAction hd Q mu h0 h1 P hP t f
  have hrep : (A : FieldPair d → ℂ) =ᵐ[Q.measure] fun ω =>
      ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω) :=
    s8_gmp_action_rep hd Q mu h0 h1 P hP t f
  have hzero := s8_gmp_action_zero hd Q mu h0 h1 P hP g
  have heq := congrArg (fun z : Lp ℂ 1 Q.measure => (z : FieldPair d → ℂ))
    (s8_shifted_gmp_action_eq_evolution_of_integrated_graph hd Q mu h0 h1 P hP hdyn t f)
  have hfactor : (Real.exp (c * (t : ℝ)) : ℂ) * (Real.exp (-c * (t : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.exp_add]
    simp
  filter_upwards [s9_gmp_endpoint_integrable hd Q mu h0 h1 P hP t f,
    hrep, hzero, Lp.coeFn_smul (Real.exp (-c * (t : ℝ))) A,
    ae_of_ae_map Probability.measurable_reduce.aemeasurable
      (Lp.coeFn_smul (Real.exp (c * (t : ℝ)) : ℂ) g)] with ω hi hr hz hs hf
  refine ⟨hi, ?_⟩
  have he : (Real.exp (-c * (t : ℝ)) : ℂ) *
      (∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω)) = g (reduce ω) := by
    have h := congrFun heq ω
    simp only [s8ShiftedGMPAction, smul_apply,
      ContinuousLinearMap.coe_restrictScalars', Real.toNNReal_coe, mul_zero,
      Real.exp_zero, one_smul, Real.toNNReal_zero] at h
    change ((Real.exp (-c * (t : ℝ)) • A : Lp ℂ 1 Q.measure) : FieldPair d → ℂ) ω =
      (s8GMPAction hd Q mu h0 h1 P hP 0 g : FieldPair d → ℂ) ω at h
    rw [hs, hz] at h
    rw [Pi.smul_apply, RCLike.real_smul_eq_coe_mul, hr] at h
    exact h
  calc
    forcedComplexEvolution Q (firstCoordinateIndex hd) (mu : ℂ) t f (reduce ω) =
        (Real.exp (c * (t : ℝ)) : ℂ) * g (reduce ω) := by
      change (((Real.exp (c * (t : ℝ)) : ℂ) • g : Lp ℂ 2 (reducedLaw Q)) :
        FieldPair d → ℂ) (reduce ω) = _
      simpa only [Pi.smul_apply, smul_eq_mul] using hf
    _ = (Real.exp (c * (t : ℝ)) : ℂ) * ((Real.exp (-c * (t : ℝ)) : ℂ) *
        (∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂P (0, ω))) := by rw [he]
    _ = _ := by rw [← mul_assoc, hfactor, one_mul]

/-- The generator of the shifted evolution is the actual forced weak graph
with the scalar shift removed. -/
theorem s8_shifted_generator_pair {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (ζ : ℂ)
    (f : (s8ShiftedForcedSemigroup Q i ζ).generatorDomain) :
    IsComplexGeneratorPair Q i ζ f
      ((s8ShiftedForcedSemigroup Q i ζ).generator f +
        (complexForceShift d Λ₀ ζ : ℂ) • (f : Lp ℂ 2 (reducedLaw Q))) := by
  apply (tendsto_shiftedForcedComplexEvolution_slope_iff Q i ζ f _).mp
  have h := (s8ShiftedForcedSemigroup Q i ζ).tendsto_generator' f
  apply h.congr
  intro t
  simp only [s8ShiftedForcedSemigroup, ContinuousLinearMap.coe_restrictScalars']
  simp only [RCLike.real_smul_eq_coe_smul (K := ℂ), RCLike.ofReal_inv]
  rfl


/-- A literal right-derivative equation for the unshifted GMP graph implies
the shifted graph derivative needed for the reversed-orbit comparison. -/
theorem s8_shifted_gmp_generator_deriv_of_graph_deriv
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (hderiv : ∀ f g, IsComplexGeneratorPair Q (firstCoordinateIndex hd) (mu : ℂ) f g →
      ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt
        (fun s => s8GMPAction hd Q mu h0 h1 P hP s.toNNReal f)
        (s8GMPAction hd Q mu h0 h1 P hP t.toNNReal g) (Ici 0) t)
    (f : (s8ShiftedForcedSemigroup Q (firstCoordinateIndex hd) (mu : ℂ)).generatorDomain)
    (t : ℝ) (ht : 0 ≤ t) :
    HasDerivWithinAt (fun s => s8ShiftedGMPAction hd Q mu h0 h1 P hP s f)
      (s8ShiftedGMPAction hd Q mu h0 h1 P hP t
        ((s8ShiftedForcedSemigroup Q (firstCoordinateIndex hd) (mu : ℂ)).generator f)) (Ioi t) t := by
  let S := s8ShiftedForcedSemigroup Q (firstCoordinateIndex hd) (mu : ℂ)
  let c := complexForceShift d Λ₀ (mu : ℂ)
  have hpair : IsComplexGeneratorPair Q (firstCoordinateIndex hd) (mu : ℂ) f
      (S.generator f + (c : ℂ) • (f : Lp ℂ 2 (reducedLaw Q))) :=
    s8_shifted_generator_pair Q (firstCoordinateIndex hd) (mu : ℂ) f
  have ha := (hderiv f (S.generator f + (c : ℂ) • (f : Lp ℂ 2 (reducedLaw Q)))
    hpair t ht).mono (show Ioi t ⊆ Ici 0 from fun s hs => ht.trans hs.le)
  have he : HasDerivWithinAt (fun s : ℝ => Real.exp (-c * s))
      (-c * Real.exp (-c * t)) (Ioi t) t := by
    convert ((Real.hasDerivAt_exp (-c * t)).comp t
      ((hasDerivAt_const t (-c)).mul (hasDerivAt_id t))).hasDerivWithinAt using 1 <;>
      try { funext s; simp only [Function.comp_apply, neg_mul] } <;> ring
  have hp := he.smul ha
  have hmap (x : Lp ℂ 2 (reducedLaw Q)) :
      s8GMPAction hd Q mu h0 h1 P hP t.toNNReal ((c : ℂ) • x) =
      c • s8GMPAction hd Q mu h0 h1 P hP t.toNNReal x := by
    rw [map_smul]
    exact (RCLike.real_smul_eq_coe_smul (K := ℂ) c _).symm
  convert hp using 1 <;>
    simp only [s8ShiftedGMPAction, smul_apply,
      ContinuousLinearMap.coe_restrictScalars', map_add, hmap, zero_mul, zero_add,
      one_mul, neg_mul, neg_smul] <;> try { funext s; rfl } <;> module

/-- The unshifted graph derivative implies the integrated shifted graph
equation. -/
theorem s8_shifted_gmp_integrated_graph_of_graph_deriv
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (hderiv : ∀ f g, IsComplexGeneratorPair Q (firstCoordinateIndex hd) (mu : ℂ) f g →
      ∀ t : ℝ, 0 ≤ t → HasDerivWithinAt
        (fun s => s8GMPAction hd Q mu h0 h1 P hP s.toNNReal f)
        (s8GMPAction hd Q mu h0 h1 P hP t.toNNReal g) (Ici 0) t)
    (x : (s8ShiftedForcedSemigroup Q (firstCoordinateIndex hd) (mu : ℂ)).generatorDomain)
    (t : ℝ) (ht : 0 ≤ t) :
    s8ShiftedGMPAction hd Q mu h0 h1 P hP t x -
        s8ShiftedGMPAction hd Q mu h0 h1 P hP 0 x =
      ∫ s in (0 : ℝ)..t, s8ShiftedGMPAction hd Q mu h0 h1 P hP s
        ((s8ShiftedForcedSemigroup Q (firstCoordinateIndex hd) (mu : ℂ)).generator x) := by
  have hc := s8_shifted_gmp_action_continuous hd Q mu h0 h1 P hP
  have he := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht
    (hc x).continuousOn
    (fun s hs => s8_shifted_gmp_generator_deriv_of_graph_deriv
      hd Q mu h0 h1 P hP hderiv x s hs.1.le)
    ((hc ((s8ShiftedForcedSemigroup Q (firstCoordinateIndex hd) (mu : ℂ)).generator x)).intervalIntegrable 0 t)
  exact he.symm

/-- The two constructions of the actual endpoint L¹ class coincide. -/
theorem s8_gmp_action_eq_dynkin_endpoint
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)) :
    s8GMPAction hd Q mu h0 h1 P hP t f =
      s13GmpEndpointL1 hd Q mu h0 h1 P hP t f := by
  apply Lp.ext
  exact (s8_gmp_action_rep hd Q mu h0 h1 P hP t f).trans
    (s13_gmp_endpoint_L1_rep hd Q mu h0 h1 P hP t f).symm

/-- The actual GMP endpoint operator satisfies the integrated complex graph
equation in L¹ of the environment law. -/
theorem s8_gmp_action_integrated_graph
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q (firstCoordinateIndex hd) (mu : ℂ) f g)
    (t : ℝ) (ht : 0 ≤ t) :
    s8GMPAction hd Q mu h0 h1 P hP t.toNNReal f -
        s8GMPAction hd Q mu h0 h1 P hP 0 f =
      ∫ s in (0 : ℝ)..t, s8GMPAction hd Q mu h0 h1 P hP s.toNNReal g := by
  have hzero : s8GMPAction hd Q mu h0 h1 P hP 0 f =
      (s13_reduced_pullback_integrable Q f).toL1 (fun ω => f (reduce ω)) := by
    apply Lp.ext
    exact (s8_gmp_action_zero hd Q mu h0 h1 P hP f).trans
      (s13_reduced_pullback_integrable Q f).coeFn_toL1.symm
  have hi : firstCoordinateIndex hd = (⟨0, by omega⟩ : Fin d) := Fin.ext rfl
  have h := s13_gmp_L1_dynkin hd Q mu h0 h1 P hP t.toNNReal f g (by simpa only [hi] using hfg)
  rw [← s8_gmp_action_eq_dynkin_endpoint hd Q mu h0 h1 P hP, ← hzero] at h
  rw [intervalIntegral.integral_of_le ht]
  simpa only [Real.coe_toNNReal _ ht, ← s8_gmp_action_eq_dynkin_endpoint hd Q mu h0 h1 P hP] using h

/-- The actual GMP endpoint operator has the right graph derivative. -/
theorem s8_gmp_action_graph_deriv
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : IsComplexGeneratorPair Q (firstCoordinateIndex hd) (mu : ℂ) f g)
    (t : ℝ) (ht : 0 ≤ t) : HasDerivWithinAt
      (fun s => s8GMPAction hd Q mu h0 h1 P hP s.toNNReal f)
      (s8GMPAction hd Q mu h0 h1 P hP t.toNNReal g) (Ici 0) t := by
  have hc : Continuous (fun s : ℝ => s8GMPAction hd Q mu h0 h1 P hP s.toNNReal g) := by
    simp_rw [s8_gmp_action_eq_dynkin_endpoint]
    exact (s13_gmp_endpoint_curve_continuous hd Q mu h0 h1 P hP g).comp continuous_real_toNNReal
  have hh := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const
      (s8GMPAction hd Q mu h0 h1 P hP 0 f)
  apply hh.hasDerivWithinAt.congr_of_mem _ ht
  intro s hs
  exact sub_eq_iff_eq_add.mp (s8_gmp_action_integrated_graph hd Q mu h0 h1 P hP f g hfg s hs)

/-- The supplied GMP reduced kernel acts as the forced evolution for this law. -/
theorem s8_gmp_reduced_kernel_action_at
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    SbxS4Dynkin.GMPReducedKernelActionAt hd Q := by
  intro mu h0 h1 P hP t f
  apply s8_gmp_endpoint_eq_evolution_of_integrated_graph hd Q mu h0 h1 P hP
  exact s8_shifted_gmp_integrated_graph_of_graph_deriv hd Q mu h0 h1 P hP
    (s8_gmp_action_graph_deriv hd Q mu h0 h1 P hP)

/-- The supplied GMP reduced kernel acts as the forced evolution for every law. -/
theorem s8_gmp_reduced_kernel_action : SbxS4Dynkin.GMPReducedKernelAction :=
  fun _ hd _ _ Q => s8_gmp_reduced_kernel_action_at hd Q

/-- The original remainder-moment conclusion follows from the regeneration tails. -/
theorem s8_remainder_moment_of_regeneration_tails
    (htail : Blueprint.node_app_u3A_regen_u2D_tailsStmt) :
    Blueprint.node_rt_u3A_remainder_u2D_momentStmt :=
  Blueprint.node_rt_u3A_remainder_u2D_moment_of_action htail s8_gmp_reduced_kernel_action

end EinsteinFull
