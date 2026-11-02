import EinsteinFull.Calculus.C17UnforcedEnvironmentInvariant
import EinsteinFull.Calculus.C22SuppliedLawDiscountedOccupation
import EinsteinFull.Calculus.C22QuenchedOccupationSubsequence
import SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.TimeChangeLaplaceUniqueness
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed

/-! Consequences of identifying the actual supplied path-law occupation with
its analytic resolvent. The identification itself is proved separately. -/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal BoundedContinuousFunction Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

/-- The quenched occupation-resolvent identity yields the annealed Laplace
identity, using the literal supplied kernel and the analytic resolvent mean. -/
theorem c17_annealed_laplace_of_occupation_resolvent
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (i : Fin d) (s : ℝ) (hs : 0 < s)
    (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (hres : ∀ᵐ ω ∂Q.measure,
      (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) *
        (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω)) =
      unforcedComplexResolvent Q i s hs
        (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ g) (reduce ω)) :
    (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) *
      (∫ ω, ∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω ∂Q.measure)) =
      (s : ℂ)⁻¹ * ∫ ω, g ω ∂reducedLaw Q := by
  rw [c17_discounted_annealed_environment_integral_swap Q K g s hs,
    integral_congr_ae hres]
  exact c17_integral_unforcedComplexResolvent_pullback Q i s hs g

/-- A bounded continuous complex function is determined on the positive
half-line by its Laplace transform at every positive rate. -/
theorem c17_complex_laplace_unique {f : ℝ → ℂ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ t, ‖f t‖ ≤ C)
    (hzero : ∀ s : ℝ, 0 < s →
      (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) * f t) = 0) :
    ∀ t : ℝ, 0 ≤ t → f t = 0 := by
  have hint (s : ℝ) (hs : 0 < s) :
      Integrable (fun t : ℝ => (Real.exp (-s * t) : ℂ) * f t)
        (volume.restrict (Set.Ioi 0)) := by
    apply (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const C)).mono'
      (((Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul hf).aestronglyMeasurable)
    exact ae_of_all _ fun t => by
      change ‖(Real.exp (-s * t) : ℂ) * f t‖ ≤ Real.exp (-s * t) * C
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hC t) (Real.exp_nonneg _)
  have hre : ∀ t : ℝ, 0 ≤ t → (f t).re = 0 := by
    apply SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.eq_zero_of_forall_integral_exp_neg_mul_eq_zero (Complex.continuous_re.comp hf) (C := C)
    · intro t
      exact (Complex.abs_re_le_norm (f t)).trans (hC t)
    · intro s hs
      have h := integral_re (hint s hs)
      rw [hzero s hs] at h
      change (∫ x : ℝ in Set.Ioi 0, ((Real.exp (-s * x) : ℂ) * f x).re) = (0 : ℂ).re at h
      simpa only [Function.comp_apply, neg_mul, Complex.zero_re, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero] using h
  have him : ∀ t : ℝ, 0 ≤ t → (f t).im = 0 := by
    apply SubdiffusiveProcess.CoarseGrainingVocab.Section7Clock.eq_zero_of_forall_integral_exp_neg_mul_eq_zero (Complex.continuous_im.comp hf) (C := C)
    · intro t
      exact (Complex.abs_im_le_norm (f t)).trans (hC t)
    · intro s hs
      have h := integral_im (hint s hs)
      rw [hzero s hs] at h
      change (∫ x : ℝ in Set.Ioi 0, ((Real.exp (-s * x) : ℂ) * f x).im) = (0 : ℂ).im at h
      simpa only [Function.comp_apply, neg_mul, Complex.zero_im, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero] using h
  intro t ht
  exact Complex.ext (by simpa using hre t ht) (by simpa using him t ht)

/-- A constant Laplace transform identifies a bounded continuous complex
function on nonnegative times. -/
theorem c17_complex_laplace_eq_constant {f : ℝ → ℂ} (hf : Continuous f)
    {C : ℝ} (hC : ∀ t, ‖f t‖ ≤ C) (z : ℂ)
    (hlap : ∀ s : ℝ, 0 < s →
      (∫ t in Set.Ioi (0 : ℝ), (Real.exp (-s * t) : ℂ) * f t) =
        (s : ℂ)⁻¹ * z) : ∀ t : ℝ, 0 ≤ t → f t = z := by
  intro t ht
  apply sub_eq_zero.mp
  apply c17_complex_laplace_unique (hf.sub continuous_const)
    (C := C + ‖z‖) (fun t => (norm_sub_le _ _).trans (add_le_add (hC t) (le_refl ‖z‖))) ?_ t ht
  intro s hs
  have he : Integrable (fun t : ℝ => (Real.exp (-s * t) : ℂ))
      (volume.restrict (Set.Ioi 0)) := by
    simpa only [Complex.ofRealCLM_apply] using Complex.ofRealCLM.integrable_comp
      (integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0)
  have hfint : Integrable (fun t : ℝ => (Real.exp (-s * t) : ℂ) * f t)
      (volume.restrict (Set.Ioi 0)) := by
    apply (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const C)).mono'
      (((Complex.continuous_ofReal.comp
        (Real.continuous_exp.comp (continuous_const.mul continuous_id))).mul hf).aestronglyMeasurable)
    exact ae_of_all _ fun t => by
      change ‖(Real.exp (-s * t) : ℂ) * f t‖ ≤ Real.exp (-s * t) * C
      rw [norm_mul, Complex.norm_of_nonneg (Real.exp_nonneg _)]
      exact mul_le_mul_of_nonneg_left (hC t) (Real.exp_nonneg _)
  have heval : (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ)) = (s : ℂ)⁻¹ := by
    rw [integral_complex_ofReal, integral_exp_mul_Ioi (neg_lt_zero.mpr hs) 0]
    simp only [mul_zero, Real.exp_zero, neg_div_neg_eq, one_div, Complex.ofReal_inv]
  change (∫ x : ℝ in Set.Ioi 0, (Real.exp (-s * x) : ℂ) * (f x - z)) = 0
  simp_rw [mul_sub]
  rw [integral_sub hfint (he.mul_const z), hlap s hs, integral_mul_const, heval, sub_self]

/-- The annealed Laplace identity fixes all nonnegative-time expectations of
an actual bounded continuous environment observation. -/
theorem c17_annealed_mean_of_laplace
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (g : BoundedContinuousFunction (FieldPair d) ℂ)
    (hlap : ∀ s : ℝ, 0 < s →
      (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) *
        (∫ ω, ∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω ∂Q.measure)) =
          (s : ℂ)⁻¹ * ∫ ρ, g ρ ∂reducedLaw Q) :
    ∀ t : ℝ≥0, (∫ ω, ∫ γ : Path d,
      g (translate (γ t) (reduce ω)) ∂K ω ∂Q.measure) =
        ∫ ρ, g ρ ∂reducedLaw Q := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  have hb : ∀ t : ℝ, ‖∫ ω, ∫ γ : Path d,
      g (translate (γ t.toNNReal) (reduce ω)) ∂K ω ∂Q.measure‖ ≤ ‖g‖ := by
    intro t
    simpa only [probReal_univ, mul_one] using
      norm_integral_le_of_norm_le_const (ae_of_all Q.measure fun ω => by
        simpa only [probReal_univ, mul_one] using
          norm_integral_le_of_norm_le_const
            (ae_of_all (K ω) fun γ => g.norm_coe_le_norm _))
  intro t
  have h := c17_complex_laplace_eq_constant
    (c17_continuous_annealed_environment_mean Q K g) hb
    (∫ ρ, g ρ ∂reducedLaw Q) hlap (t : ℝ) (by positivity)
  simpa only [Real.toNNReal_coe] using h

/-- Complex bounded continuous tests determine a finite Borel measure. -/
theorem c17_measure_ext_of_complex_tests
    {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [HasOuterApproxClosed Ω]
    [BorelSpace Ω] {μ ν : Measure Ω} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ g : Ω →ᵇ ℂ, ∫ x, g x ∂μ = ∫ x, g x ∂ν) : μ = ν := by
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hf := h (f.comp Complex.ofReal Complex.isometry_ofReal.lipschitzWith)
  simpa only [BoundedContinuousFunction.comp_apply, integral_complex_ofReal,
    Complex.ofReal_inj] using hf

/-- Bounded annealed means determine the marginal of the supplied path law. -/
theorem c17_unforced_annealed_marginal_of_bounded_means
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (c17_unforced_annealed_mean :
      ∀ (g : BoundedContinuousFunction (FieldPair d) ℂ) (t : ℝ≥0),
        (∫ ω, ∫ γ : Path d,
          g (translate (γ t) (reduce ω)) ∂K ω ∂Q.measure) =
          ∫ ω, g ω ∂reducedLaw Q) :
    ∀ t : ℝ≥0, Measure.map
      (fun z : FieldPair d × Path d => translate (z.2 t) (reduce z.1))
      (Q.measure ⊗ₘ K) = reducedLaw Q := by
  intro t
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : IsProbabilityMeasure Q.measure := Q.probability
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hm : Continuous (fun z : FieldPair d × Path d =>
      translate (z.2 t) (reduce z.1)) :=
    Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_snd.prodMk continuous_const)).prodMk
        (Probability.continuous_reduce.comp continuous_fst))
  apply c17_measure_ext_of_complex_tests
  intro g
  have hi : Integrable (fun z : FieldPair d × Path d =>
      g (translate (z.2 t) (reduce z.1))) (Q.measure ⊗ₘ K) :=
    Integrable.of_bound (g.continuous.comp hm).aestronglyMeasurable ‖g‖
      (ae_of_all _ fun z => g.norm_coe_le_norm _)
  calc
    _ = ∫ z : FieldPair d × Path d,
        g (translate (z.2 t) (reduce z.1)) ∂(Q.measure ⊗ₘ K) :=
      integral_map hm.measurable.aemeasurable g.continuous.aestronglyMeasurable
    _ = ∫ ω, ∫ γ : Path d,
        g (translate (γ t) (reduce ω)) ∂K ω ∂Q.measure := Measure.integral_compProd hi
    _ = _ := c17_unforced_annealed_mean g t

/-- Identified annealed observations determine the literal environment marginal. -/
theorem c17_environment_marginal_of_annealed_mean
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K] (t : ℝ≥0)
    (hmean : ∀ g : FieldPair d →ᵇ ℂ,
      (∫ ω, ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂K ω ∂Q.measure) =
        ∫ ρ, g ρ ∂reducedLaw Q) :
    c2EnvironmentKernel K t ∘ₘ Q.measure = reducedLaw Q := by
  letI : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  letI : IsProbabilityMeasure Q.measure := Q.probability
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  apply c17_measure_ext_of_complex_tests
  intro g
  have hi : Integrable g (c2EnvironmentKernel K t ∘ₘ Q.measure) :=
    Integrable.of_bound g.continuous.aestronglyMeasurable ‖g‖
      (ae_of_all _ fun x => g.norm_coe_le_norm x)
  calc
    _ = ∫ ω, ∫ η, g η ∂c2EnvironmentKernel K t ω ∂Q.measure := by
      rw [Measure.comp_eq_comp_const_apply] at hi ⊢
      simpa using ProbabilityTheory.Kernel.integral_comp hi
    _ = ∫ ω, ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂K ω ∂Q.measure := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => by
        change (∫ η, g η ∂c2EnvironmentKernel K t ω) =
          ∫ γ : Path d, g (translate (γ t) (reduce ω)) ∂K ω
        rw [c2EnvironmentKernel_apply]
        have hm : Measurable (fun γ : Path d => translate (γ t) (reduce ω)) :=
          (measurable_c2EnvironmentAt t).comp (measurable_const.prodMk measurable_id)
        exact integral_map hm.aemeasurable g.continuous.aestronglyMeasurable
    _ = _ := hmean g

/-- The supplied-kernel occupation-resolvent identity implies invariance of
its actual environment marginal. -/
theorem c17_environment_marginal_of_occupation_resolvent
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K] (i : Fin d)
    (hres : ∀ (g : FieldPair d →ᵇ ℂ) (s : ℝ) (hs : 0 < s),
      ∀ᵐ ω ∂Q.measure,
        (∫ t : ℝ in Set.Ioi 0, (Real.exp (-s * t) : ℂ) *
          (∫ γ : Path d, g (translate (γ t.toNNReal) (reduce ω)) ∂K ω)) =
        unforcedComplexResolvent Q i s hs
          (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ g) (reduce ω)) :
    ∀ t : ℝ≥0, c2EnvironmentKernel K t ∘ₘ Q.measure = reducedLaw Q := by
  intro t
  apply c17_environment_marginal_of_annealed_mean Q K t
  intro g
  apply c17_annealed_mean_of_laplace Q K g ?_ t
  intro s hs
  exact c17_annealed_laplace_of_occupation_resolvent Q K i s hs g (hres g s hs)


/-- Under a supplied-kernel occupation estimate, L2-small residuals have
vanishing annealed discounted absolute occupation. -/
theorem c17_tendsto_discounted_occupation_of_L2_bound
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d))
    (s C : ℝ)
    (hbound : ∀ (r : FieldPair d → ℝ), Measurable r →
      ∀ hr : MemLp r 2 (reducedLaw Q),
      Integrable (fun p : ℝ × (FieldPair d × Path d) =>
        Real.exp (-s * p.1) * |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
        ((volume.restrict (Set.Ioi 0)).prod (Q.measure ⊗ₘ K)) ∧
      (∫ ω, (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        (∫ γ : Path d, |r (translate (γ t.toNNReal) (reduce ω))| ∂K ω)) ∂Q.measure)
          ≤ C * ‖hr.toLp r‖)
    (r : ℕ → FieldPair d → ℝ) (hm : ∀ n, Measurable (r n))
    (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Filter.Tendsto (fun n => ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => ∫ ω, (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
      (∫ γ : Path d, |r n (translate (γ t.toNNReal) (reduce ω))| ∂K ω)) ∂Q.measure)
      Filter.atTop (𝓝 0) := by
  have hu : Filter.Tendsto (fun n => C * ‖(hr n).toLp (r n)‖) Filter.atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul hlim
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hu
  · exact Filter.Eventually.of_forall fun n => integral_nonneg fun ω =>
      integral_nonneg fun t => mul_nonneg (Real.exp_nonneg _) (integral_nonneg fun γ => abs_nonneg _)
  · exact Filter.Eventually.of_forall fun n => (hbound (r n) (hm n) (hr n)).2


/-- Joint integrability supplies integrable timewise expected absolute values
for almost every initial environment. -/
theorem c17_integrable_time_expected_norm
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (κ : Kernel β γ) [IsSFiniteKernel κ] (F : α × (β × γ) → ℝ)
    (hF : Integrable F (μ.prod (ν ⊗ₘ κ))) :
    ∀ᵐ b ∂ν, Integrable (fun a => ∫ c, ‖F (a, b, c)‖ ∂κ b) μ := by
  let G : (α × β) × γ → ℝ := fun p => F (p.1.1, p.1.2, p.2)
  have hG : Integrable G ((μ.prod ν) ⊗ₘ Kernel.prodMkLeft α κ) := by
    apply (integrable_map_equiv MeasurableEquiv.prodAssoc F).mp
    rw [c22_prod_compProd_assoc]
    exact hF
  have hI : Integrable (fun p : α × β => ∫ c, ‖G (p, c)‖ ∂κ p.2) (μ.prod ν) := by
    simpa only [Kernel.prodMkLeft_apply] using
      ((Measure.integrable_compProd_iff hG.aestronglyMeasurable).mp hG).2
  simpa only [G] using hI.prod_left_ae



/-- Joint integrability supplies path integrability for almost every
initial environment and almost every time. -/
theorem c17_integrable_path_slices
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (κ : Kernel β γ) [IsSFiniteKernel κ] (F : α × (β × γ) → ℝ)
    (hF : Integrable F (μ.prod (ν ⊗ₘ κ))) :
    ∀ᵐ b ∂ν, ∀ᵐ a ∂μ, Integrable (fun c => F (a, b, c)) (κ b) := by
  let G : (α × β) × γ → ℝ := fun p => F (p.1.1, p.1.2, p.2)
  have hG : Integrable G ((μ.prod ν) ⊗ₘ Kernel.prodMkLeft α κ) := by
    apply (integrable_map_equiv MeasurableEquiv.prodAssoc F).mp
    rw [c22_prod_compProd_assoc]
    exact hF
  have htime : ∀ᵐ p ∂(μ.prod ν), Integrable (fun c => F (p.1, p.2, c)) (κ p.2) := by
    simpa only [Kernel.prodMkLeft_apply, G] using
      ((Measure.integrable_compProd_iff hG.aestronglyMeasurable).mp hG).1
  have hswap : ∀ᵐ p ∂(ν.prod μ), Integrable (fun c => F (p.2, p.1, c)) (κ p.1) := by
    have hm : ∀ᵐ p ∂((ν.prod μ).map Prod.swap),
        Integrable (fun c => F (p.1, p.2, c)) (κ p.2) := by
      rw [Measure.prod_swap]
      exact htime
    exact ae_of_ae_map measurable_swap.aemeasurable hm
  exact Measure.ae_ae_of_ae_prod hswap


/-- A spatial full-measure property holds for almost every positive time along
almost every path under the supplied origin law. -/
theorem c17_unforced_mp_ae_path_of_spatial_ae
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d))
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    {p : Vec d → Prop} (hp : ∀ᵐ x ∂(volume : Measure (Vec d)), p x) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂K ω,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)), p (γ t.toNNReal) := by
  filter_upwards [c17_unforced_mp_averaged_occupation_ac_of_two_le (hpath := hpath) hd Q K hK]
    with ω hocc
  exact c16_ae_path_of_averaged_occupation (K ω) hocc hp

/-- The supplied occupation bound turns L2 convergence into a quenched
subsequence with vanishing discounted absolute occupation. -/
theorem c17_residual_quenched_subsequence
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (s C : ℝ)
    (hbound : ∀ (r : FieldPair d → ℝ), Measurable r →
      ∀ hr : MemLp r 2 (reducedLaw Q),
      Integrable (fun p : ℝ × (FieldPair d × Path d) =>
        Real.exp (-s * p.1) * |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K)) ∧
      (∫ ω, (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        (∫ γ : Path d, |r (translate (γ t.toNNReal) (reduce ω))| ∂K ω)) ∂Q.measure)
          ≤ C * ‖hr.toLp r‖)
    (r : ℕ → FieldPair d → ℝ) (hm : ∀ n, Measurable (r n))
    (hr : ∀ n, MemLp (r n) 2 (reducedLaw Q))
    (hlim : Tendsto (fun n => ‖(hr n).toLp (r n)‖) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Tendsto (fun n => ∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) *
        (∫ γ : Path d, |r (ns n) (translate (γ u.toNNReal) (reduce ω))| ∂K ω))
        atTop (𝓝 0) := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  have hi : ∀ n, Integrable (fun a : ℝ × (FieldPair d × Path d) =>
      Real.exp (-s * a.1) * |r n (translate (a.2.2 a.1.toNNReal) (reduce a.2.1))|)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K)) :=
    fun n => (hbound (r n) (hm n) (hr n)).1
  have hann := c17_tendsto_discounted_occupation_of_L2_bound Q K s C hbound r hm hr hlim
  have heq : ∀ n, (∫ ω, (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
      (∫ γ : Path d, |r n (translate (γ t.toNNReal) (reduce ω))| ∂K ω)) ∂Q.measure) =
      ∫ a : ℝ × (FieldPair d × Path d), Real.exp (-s * a.1) *
        |r n (translate (a.2.2 a.1.toNNReal) (reduce a.2.1))|
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K)) := by
    intro n
    have h := c22_integral_prod_compProd_swap (volume.restrict (Set.Ioi (0 : ℝ))) Q.measure K
      (fun a : ℝ × (FieldPair d × Path d) => Real.exp (-s * a.1) *
        |r n (translate (a.2.2 a.1.toNNReal) (reduce a.2.1))|)
      (fun a => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)) (hi n)
    simp_rw [integral_const_mul] at h
    exact h.symm
  have hjoint : Tendsto (fun n => ∫ a : ℝ × (FieldPair d × Path d),
      Real.exp (-s * a.1) * |r n (translate (a.2.2 a.1.toNNReal) (reduce a.2.1))|
      ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K))) atTop (𝓝 0) := by
    simpa only [← heq] using hann
  exact c22_discounted_occupation_quenched_subsequence Q K s r hi hjoint

/-- An L2 occupation bound transports reduced-law almost-everywhere
zero observations to the supplied time-environment-path law. -/
theorem c17_occupation_ae_zero
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (s C : ℝ) (r : FieldPair d → ℝ) (hr : MemLp r 2 (reducedLaw Q))
    (hz : r =ᵐ[reducedLaw Q] 0)
    (hi : Integrable (fun p : ℝ × (FieldPair d × Path d) =>
      Real.exp (-s * p.1) * |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
      ((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K)))
    (hb : (∫ ω, (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
      (∫ γ : Path d, |r (translate (γ t.toNNReal) (reduce ω))| ∂K ω)) ∂Q.measure)
        ≤ C * ‖hr.toLp r‖) :
    ∀ᵐ p ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K)),
      r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1)) = 0 := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  have hlp : hr.toLp r = 0 := by
    have hzero : MemLp (0 : FieldPair d → ℝ) 2 (reducedLaw Q) := MemLp.zero
    exact (MemLp.toLp_congr hr hzero hz).trans (MemLp.toLp_zero hzero)
  have hswap := c22_integral_prod_compProd_swap (volume.restrict (Set.Ioi (0 : ℝ))) Q.measure K
    (fun p : ℝ × (FieldPair d × Path d) => Real.exp (-s * p.1) *
      |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
    (fun p => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)) hi
  simp_rw [integral_const_mul] at hswap
  have hn : ∀ p : ℝ × (FieldPair d × Path d), 0 ≤ Real.exp (-s * p.1) *
      |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))| :=
    fun p => mul_nonneg (Real.exp_nonneg _) (abs_nonneg _)
  have hzero : (∫ p : ℝ × (FieldPair d × Path d), Real.exp (-s * p.1) *
      |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|
      ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K))) = 0 := by
    apply le_antisymm
    · rw [hswap]
      simpa [hlp] using hb
    · exact integral_nonneg hn
  have hae := (integral_eq_zero_iff_of_nonneg hn hi).mp hzero
  filter_upwards [hae] with p hp
  have hpos := Real.exp_pos (-s * p.1)
  exact abs_eq_zero.mp ((mul_eq_zero.mp hp).resolve_left (ne_of_gt hpos))

/-- Null sets under the reduced law have zero discounted occupation for the
same supplied kernel. -/
theorem c17_occupation_avoids_null_set
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (s C : ℝ)
    (hbound : ∀ (r : FieldPair d → ℝ), Measurable r →
      ∀ hr : MemLp r 2 (reducedLaw Q),
      Integrable (fun p : ℝ × (FieldPair d × Path d) =>
        Real.exp (-s * p.1) * |r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|)
        ((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K)) ∧
      (∫ ω, (∫ t : ℝ in Set.Ioi 0, Real.exp (-s*t) *
        (∫ γ : Path d, |r (translate (γ t.toNNReal) (reduce ω))| ∂K ω)) ∂Q.measure)
          ≤ C * ‖hr.toLp r‖)
    (N : Set (FieldPair d)) (hNm : MeasurableSet N) (hN : reducedLaw Q N = 0) :
    ∀ᵐ p ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K)),
      translate (p.2.2 p.1.toNNReal) (reduce p.2.1) ∉ N := by
  let r : FieldPair d → ℝ := N.indicator (fun _ => 1)
  have hm : Measurable r := measurable_const.indicator hNm
  have hnot : ∀ᵐ w ∂reducedLaw Q, w ∉ N := by
    rw [ae_iff]
    simpa using hN
  have hz : r =ᵐ[reducedLaw Q] 0 := by
    filter_upwards [hnot] with w hw
    simp [r, Set.indicator_of_notMem hw]
  have hr : MemLp r 2 (reducedLaw Q) :=
    MemLp.ae_eq hz.symm (MemLp.zero)
  have h := hbound r hm hr
  have he := c17_occupation_ae_zero Q K s C r hr hz h.1 h.2
  filter_upwards [he] with p hp
  intro hpN
  have : r (translate (p.2.2 p.1.toNNReal) (reduce p.2.1)) = 1 := by
    simp [r, hpN]
  linarith


/-- Disintegrate joint almost-everywhere facts in environment, time and path order. -/
theorem c17_occupation_ae_quenched
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (κ : Kernel β γ) [IsSFiniteKernel κ] (P : α → β → γ → Prop)
    (h : ∀ᵐ p ∂(μ.prod (ν ⊗ₘ κ)), P p.1 p.2.1 p.2.2) :
    ∀ᵐ b ∂ν, ∀ᵐ a ∂μ, ∀ᵐ c ∂κ b, P a b c := by
  have hassoc : ∀ᵐ p ∂(((μ.prod ν) ⊗ₘ Kernel.prodMkLeft α κ)),
      P p.1.1 p.1.2 p.2 := by
    have hm : ∀ᵐ p ∂(((μ.prod ν) ⊗ₘ Kernel.prodMkLeft α κ).map
        MeasurableEquiv.prodAssoc), P p.1 p.2.1 p.2.2 := by
      rw [c22_prod_compProd_assoc]
      exact h
    exact ae_of_ae_map MeasurableEquiv.prodAssoc.measurable.aemeasurable hm
  have htime : ∀ᵐ p ∂(μ.prod ν), ∀ᵐ c ∂κ p.2, P p.1 p.2 c := by
    simpa only [Kernel.prodMkLeft_apply] using Measure.ae_ae_of_ae_compProd hassoc
  have hswap : ∀ᵐ p ∂(ν.prod μ), ∀ᵐ c ∂κ p.1, P p.2 p.1 c := by
    have hm : ∀ᵐ p ∂((ν.prod μ).map Prod.swap),
        ∀ᵐ c ∂κ p.2, P p.1 p.2 c := by
      rw [Measure.prod_swap]
      exact htime
    exact ae_of_ae_map measurable_swap.aemeasurable hm
  exact Measure.ae_ae_of_ae_prod hswap


/-- A reduced-law null set is avoided for almost every positive time by
almost every path of the supplied unforced law. -/
theorem c17_unforced_environment_null_occupation_of_spatial_ac
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d))
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (N : Set (FieldPair d)) (hNm : MeasurableSet N) (hN : reducedLaw Q N = 0) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂K ω,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        translate (γ t.toNNReal) (reduce ω) ∉ N := by
  letI : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hn : ∀ᵐ ρ ∂reducedLaw Q, ρ ∉ N := by
    simpa only [ae_iff, not_not, Set.setOf_mem_eq] using hN
  have horbit : ∀ᵐ ρ ∂reducedLaw Q, ∀ᵐ x ∂(volume : Measure (Vec d)),
      translate x ρ ∉ N := by
    apply (Measure.ae_ae_comm (μ := (volume : Measure (Vec d)))
      (ν := reducedLaw Q) (hNm.preimage Probability.continuous_translate.measurable).compl).mp
    exact ae_of_all _ fun x =>
      (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hn
  have hpull : ∀ᵐ ω ∂Q.measure, ∀ᵐ x ∂(volume : Measure (Vec d)),
      translate x (reduce ω) ∉ N := by
    exact ae_of_ae_map Probability.measurable_reduce.aemeasurable horbit
  filter_upwards [hpull,
    c17_unforced_mp_averaged_occupation_ac_of_two_le (hpath := hpath) hd Q K hK] with ω hω hocc
  exact c16_ae_path_of_averaged_occupation (K ω) hocc hω

/-- A measurable reduced-law full set holds under the supplied joint occupation. -/
theorem c17_unforced_occupation_ae_mem
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d))
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (S : Set (FieldPair d)) (hS : MeasurableSet S) (hN : reducedLaw Q Sᶜ = 0) :
    ∀ᵐ p ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K)),
      translate (p.2.2 p.1.toNNReal) (reduce p.2.1) ∈ S := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  have henv : Measurable (fun p : ℝ × (FieldPair d × Path d) =>
      translate (p.2.2 p.1.toNNReal) (reduce p.2.1)) := by
    have heval : Continuous (fun p : ℝ × (FieldPair d × Path d) =>
        p.2.2 p.1.toNNReal) :=
      continuous_eval.comp (continuous_snd.snd.prodMk
        (continuous_real_toNNReal.comp continuous_fst))
    exact (Probability.continuous_translate.comp
      (heval.prodMk (Probability.continuous_reduce.comp continuous_snd.fst))).measurable
  have hm : MeasurableSet {p : ℝ × (FieldPair d × Path d) |
      translate (p.2.2 p.1.toNNReal) (reduce p.2.1) ∈ S} := hS.preimage henv
  have hocc := c17_unforced_environment_null_occupation_of_spatial_ac (hpath := hpath) hd Q K hK Sᶜ hS.compl hN
  have hE : MeasurableSet {p : (FieldPair d × Path d) × ℝ |
      translate (p.1.2 p.2.toNNReal) (reduce p.1.1) ∈ S} :=
    hm.preimage (by fun_prop : Measurable (fun p : (FieldPair d × Path d) × ℝ => (p.2, p.1)))
  have hgood : MeasurableSet {z : FieldPair d × Path d |
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        translate (z.2 t.toNNReal) (reduce z.1) ∈ S} := by
    simp only [ae_iff]
    exact measurableSet_eq_fun (measurable_measure_prodMk_left hE.compl) measurable_const
  have hpath' : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂K ω,
      ∀ᵐ t ∂volume.restrict (Set.Ioi (0 : ℝ)),
        translate (γ t.toNNReal) (reduce ω) ∈ S := by
    simpa only [Set.mem_compl_iff, not_not] using hocc
  have hpair := Measure.ae_compProd_of_ae_ae hgood hpath'
  have hjoint : ∀ᵐ p ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K)),
      translate (p.2.2 p.1.toNNReal) (reduce p.2.1) ∈ S := by
    apply (Measure.ae_prod_iff_ae_ae hm).2
    exact (Measure.ae_ae_comm hE).mp hpair
  exact hjoint

/-- Bounded observations converging under the reduced law converge in the
actual discounted occupation of the supplied unforced process. -/
theorem c17_unforced_bounded_observation_discounted_tendsto_zero
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (s : ℝ) (hs : 0 < s) (r : ℕ → FieldPair d → ℝ)
    (hr : ∀ n, Measurable (r n)) {M : ℝ}
    (hbound : ∀ n ω, |r n ω| ≤ M)
    (hlim : ∀ᵐ ω ∂reducedLaw Q,
      Filter.Tendsto (fun n => r n ω) Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n =>
      ∫ p : ℝ × (FieldPair d × Path d), Real.exp (-s * p.1) *
        |r n (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K)))
      Filter.atTop (𝓝 0) := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  let S : Set (FieldPair d) := {ω | Tendsto (fun n => r n ω) atTop (𝓝 0)}
  have hS : MeasurableSet S := measurableSet_tendsto (𝓝 0) hr
  have hN : reducedLaw Q Sᶜ = 0 := by
    simpa only [S, ae_iff, Set.compl_setOf] using hlim
  have hjoint := c17_unforced_occupation_ae_mem (hpath := hpath) hd Q K hK S hS hN
  have hconv : ∀ᵐ p ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K)),
      Tendsto (fun n => Real.exp (-s * p.1) *
        |r n (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))|) atTop (𝓝 0) := by
    filter_upwards [hjoint] with p hp
    simpa using hp.abs.const_mul (Real.exp (-s * p.1))
  simpa using (tendsto_integral_of_dominated_convergence
    (fun p : ℝ × (FieldPair d × Path d) => Real.exp (-s * p.1) * M)
    (fun n => (c17_measurable_discounted_occupation_integrand (r n) (hr n) s).aestronglyMeasurable)
    (((integrableOn_exp_mul_Ioi (neg_lt_zero.mpr hs) 0).mul_const M).comp_fst (Q.measure ⊗ₘ K))
    (fun n => ae_of_all _ fun p => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _) (abs_nonneg _))]
      exact mul_le_mul_of_nonneg_left (hbound n _) (Real.exp_nonneg _)) hconv)

/-- Bounded reduced-law convergence has a quenched discounted-occupation
subsequence for the supplied unforced kernel. -/
theorem c17_unforced_bounded_observation_quenched_subsequence
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (s : ℝ) (hs : 0 < s) (r : ℕ → FieldPair d → ℝ)
    (hr : ∀ n, Measurable (r n)) {M : ℝ}
    (hbound : ∀ n ω, |r n ω| ≤ M)
    (hlim : ∀ᵐ ω ∂reducedLaw Q, Tendsto (fun n => r n ω) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Tendsto (fun n => ∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) *
        (∫ γ : Path d, |r (ns n) (translate (γ u.toNNReal) (reduce ω))| ∂K ω))
        atTop (𝓝 0) := by
  apply c22_discounted_occupation_quenched_subsequence Q K s r
  · exact fun n => c17_integrable_discounted_occupation_of_bounded Q K
      (r n) (hr n) M (hbound n) s hs
  · exact c17_unforced_bounded_observation_discounted_tendsto_zero
      (hpath := hpath) hd Q K hK s hs r hr hbound hlim

/-- Complex bounded observations converge in the discounted occupation norm. -/
theorem c17_unforced_complex_bounded_observation_discounted_tendsto_zero
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (s : ℝ) (hs : 0 < s) (r : ℕ → FieldPair d → ℂ)
    (hr : ∀ n, Measurable (r n)) {M : ℝ}
    (hbound : ∀ n ω, ‖r n ω‖ ≤ M)
    (hlim : ∀ᵐ ω ∂reducedLaw Q, Tendsto (fun n => r n ω) atTop (𝓝 0)) :
    Tendsto (fun n =>
      ∫ p : ℝ × (FieldPair d × Path d), Real.exp (-s * p.1) *
        ‖r n (translate (p.2.2 p.1.toNNReal) (reduce p.2.1))‖
        ∂((volume.restrict (Set.Ioi (0 : ℝ))).prod (Q.measure ⊗ₘ K)))
      atTop (𝓝 0) := by
  have h := c17_unforced_bounded_observation_discounted_tendsto_zero
    (hpath := hpath) hd Q K hK s hs (fun n ω => ‖r n ω‖) (fun n => (hr n).norm)
    (fun n ω => by simpa using hbound n ω)
    (by filter_upwards [hlim] with ω hω; simpa using hω.norm)
  simpa only [abs_of_nonneg (norm_nonneg _)] using h

/-- Complex bounded observations admit a quenched discounted-occupation
subsequence for the supplied unforced kernel. -/
theorem c17_unforced_complex_bounded_observation_quenched_subsequence
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (hpath : PathwiseAt Q)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator ⟨0, by omega⟩ ω 0) 0 (K ω))
    (s : ℝ) (hs : 0 < s) (r : ℕ → FieldPair d → ℂ)
    (hr : ∀ n, Measurable (r n)) {M : ℝ}
    (hbound : ∀ n ω, ‖r n ω‖ ≤ M)
    (hlim : ∀ᵐ ω ∂reducedLaw Q, Tendsto (fun n => r n ω) atTop (𝓝 0)) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ ∀ᵐ ω ∂Q.measure,
      Tendsto (fun n => ∫ u : ℝ in Set.Ioi 0, Real.exp (-s * u) *
        (∫ γ : Path d, ‖r (ns n) (translate (γ u.toNNReal) (reduce ω))‖ ∂K ω))
        atTop (𝓝 0) := by
  have h := c17_unforced_bounded_observation_quenched_subsequence
    (hpath := hpath) hd Q K hK s hs (fun n ω => ‖r n ω‖) (fun n => (hr n).norm)
    (fun n ω => by simpa using hbound n ω)
    (by filter_upwards [hlim] with ω hω; simpa using hω.norm)
  simpa only [abs_of_nonneg (norm_nonneg _)] using h

end EinsteinFull
