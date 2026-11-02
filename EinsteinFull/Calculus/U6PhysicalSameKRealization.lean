import EinsteinFull.Calculus.C4FoundationPhysicalLawUniqueness
import EinsteinFull.Calculus.U5PhysicalPolynomialOccupation
import EinsteinFull.Calculus.U6PhysicalSuppliedCompensator
import EinsteinFull.Calculus.U6BoundedPhysicalResolvent
import EinsteinFull.Calculus.U6PhysicalPathMoments

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped ENNReal NNReal Topology

noncomputable section
namespace EinsteinFull

theorem u6_physical_same_kernel_realization_and_mp
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (hSmooth : IsSmoothFieldPair ω) :
    ∃ K : ProbabilityTheory.Kernel (Vec d) (Path d),
      ProbabilityTheory.IsMarkovKernel K ∧
      (∀ I : Finset ℝ≥0,
        K.map (MarkovProcess.ContinuousPath.finsetEvaluation I) =
          MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
            (Blueprint.gmpPhysicalC0KernelSemigroup hd ω lam Λ hΛ hω hSmooth) I) ∧
      ∀ x : Vec d, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω lam) x (K x) := by
  obtain ⟨K, ⟨hK, hfdd⟩, _⟩ :=
    Blueprint.gmpPhysicalC0KernelSemigroup_existsUnique_continuous_realization
      hd ω lam Λ hΛ hω hSmooth
  let : ProbabilityTheory.IsMarkovKernel K := hK
  exact ⟨K, hK, hfdd, fun x =>
    c4_gmpPhysical_realization_solves_martingale_problem hd ω lam Λ hΛ hω hSmooth K hfdd x⟩

#print axioms u6_physical_same_kernel_realization_and_mp

/-- A nonnegative integrable translation kernel times a bounded measurable
pairing is integrable against a finite spatial measure and volume. -/
theorem u6_integrable_kernel_pairing
    {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    {κ : Vec d → ℝ} (hc : Continuous κ) (h0 : ∀ w, 0 ≤ κ w)
    (hi : Integrable κ (volume : Measure (Vec d)))
    {G : Vec d → Vec d → ℝ} (hG : Measurable (Function.uncurry G))
    {B : ℝ} (hB : ∀ z y, |G z y| ≤ B) :
    Integrable (fun p : Vec d × Vec d => κ (p.1 - p.2) * G p.1 p.2)
      (μ.prod volume) := by
  have hmκ : AEStronglyMeasurable (fun p : Vec d × Vec d => κ (p.1 - p.2))
      (μ.prod volume) :=
    (hc.comp (continuous_fst.sub continuous_snd)).measurable.aestronglyMeasurable
  have hκprod : Integrable (fun p : Vec d × Vec d => κ (p.1 - p.2))
      (μ.prod volume) := by
    apply (integrable_prod_iff hmκ).mpr
    refine ⟨Filter.Eventually.of_forall (fun z => hi.comp_sub_left z), ?_⟩
    have heq : (fun z : Vec d => ∫ y, ‖κ (z - y)‖) = fun _ => ∫ w, κ w := by
      funext z
      simp_rw [Real.norm_eq_abs, abs_of_nonneg (h0 _)]
      exact integral_sub_left_eq_self κ volume z
    rw [heq]
    exact integrable_const _
  refine (hκprod.mul_const B).mono'
    (((hc.measurable.comp (measurable_fst.sub measurable_snd)).mul hG).aestronglyMeasurable) ?_
  filter_upwards [] with p
  rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (h0 _), Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (hB _ _) (h0 _)

/-- The frozen physical generator side of the polynomial commutation is
product-integrable for every finite spatial measure, including singular ones. -/
theorem u6_integrable_polynomial_frozen_generator
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    Integrable (fun p : Vec d × Vec d =>
      c16NormalizedPolynomialKernel r (d + 1) (p.1 - p.2) *
        External.Draft.svGenerator (fun _ => ω.1 p.1)
          (fun _ => physicalDrift ω i lam p.1) f p.2) (μ.prod volume) := by
  have hdm : (d : ℝ) < 2 * ((d + 1 : ℕ) : ℝ) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast
    linarith
  obtain ⟨hpos, hc, hi, _⟩ :=
    c16_normalized_polynomial_kernel_properties (d := d) hr (d + 1) hdm
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := physical_svHypotheses hΛ hω i lam
  have hcoef : BddCoef (⇑ω.1) (physicalDrift ω i lam) (max Ma Mb) :=
    ⟨fun k j => (hA.matrix_elem k j).measurable,
      fun k => (measurable_pi_apply k).comp hb,
      fun y k j => (hAb y k j).trans (le_max_left _ _),
      fun y k => (hbb y k).trans (le_max_right _ _)⟩
  obtain ⟨m, hm⟩ := exists_inH hf hfc
  have hconst (z : Vec d) : BddCoef (fun _ => ω.1 z)
      (fun _ => physicalDrift ω i lam z) (max Ma Mb) :=
    ⟨fun _ _ => measurable_const, fun _ => measurable_const,
      fun _ => hcoef.Ab z, fun _ => hcoef.bb z⟩
  apply u6_integrable_kernel_pairing μ hc.continuous (fun w => (hpos w).le) hi
    (G := fun z y => External.Draft.svGenerator (fun _ => ω.1 z)
      (fun _ => physicalDrift ω i lam z) f y)
    (c16_bddCoef_measurable_frozen_generator hcoef f)
  exact fun z y => (hconst z).gen_bound hm y

/-- Uniform first and second derivative bounds on a smooth kernel control the
literal physical generator uniformly over all translations and evaluation points. -/
theorem u6_physical_generator_uniform_translates
    {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (i : Fin d) (lam : ℝ) {κ : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hB : ∃ B : ℝ, ∀ k ≤ 2, ∀ z : Vec d, ‖iteratedFDeriv ℝ k κ z‖ ≤ B) :
    ∃ C : ℝ, ∀ z y, |physicalGenerator i ω lam (fun w => κ (w - y)) z| ≤ C := by
  obtain ⟨B, hB⟩ := hB
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (by omega) 0)
  obtain ⟨K, _, hK⟩ := c4_physical_generator_quantitative hΛ hω i lam
  let H : ℝ≥0 := Real.toNNReal ((d : ℝ) * B)
  refine ⟨K * (B + H), ?_⟩
  intro z y
  have hs : ContDiff ℝ (⊤ : ℕ∞) (fun w : Vec d => κ (w - y)) :=
    hκ.comp (contDiff_id.sub contDiff_const)
  have hb : ∀ k ≤ 2, ∀ w : Vec d,
      ‖iteratedFDeriv ℝ k (fun v : Vec d => κ (v - y)) w‖ ≤ B := by
    intro k hk w
    rw [iteratedFDeriv_comp_sub (𝕜 := ℝ) (f := κ) k y w]
    exact hB k hk (w - y)
  have hc (w : Vec d) := c16_test_coordinate_derivative_bounds hs hb w
  have hgrad : ∀ w j, |coordinateDerivative j (fun v => κ (v - y)) w| ≤ B :=
    fun w j => (hc w).1 j
  have hlip (j : Fin d) : LipschitzWith H
      (fun w => coordinateDerivative j (fun v => κ (v - y)) w) := by
    apply lipschitzWith_of_coordinateDerivative_le
    · exact (((contDiff_two_of_top hs).fderiv_right
        (le_of_eq one_add_one_eq_two)).clm_apply contDiff_const).differentiable (by simp)
    · intro w k
      exact (hc w).2 k j
  exact hK (fun w => κ (w - y)) B H hB0 hgrad hlip z

/-- A bounded jointly measurable pairing times an integrable continuous test
is integrable for every finite spatial measure. -/
theorem u6_integrable_bounded_pairing_mul_test
    {d : ℕ} (μ : Measure (Vec d)) [IsFiniteMeasure μ]
    {H : Vec d → Vec d → ℝ} (hH : Measurable (Function.uncurry H))
    {B : ℝ} (hB : ∀ z y, |H z y| ≤ B)
    {f : Vec d → ℝ} (hf : Continuous f)
    (hfi : Integrable f (volume : Measure (Vec d))) :
    Integrable (fun p : Vec d × Vec d => H p.1 p.2 * f p.2)
      (μ.prod volume) := by
  have hbase : Integrable (fun p : Vec d × Vec d => B * ‖f p.2‖)
      (μ.prod volume) := by
    simpa only [one_mul, mul_one, mul_comm] using
      ((integrable_const (1 : ℝ) : Integrable (fun _ : Vec d => (1 : ℝ)) μ).mul_prod
        hfi.norm).mul_const B
  refine hbase.mono' ((hH.mul (hf.measurable.comp measurable_snd)).aestronglyMeasurable) ?_
  filter_upwards [] with p
  rw [norm_mul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_right (hB _ _) (norm_nonneg _)

/-- A finite-occupation generator commutation follows from product
integrability and the corresponding spatial pairing at almost every occupied
point. This isolates the Fubini step without assuming an occupation density. -/
theorem u6_commutation_of_spatial_pairing
    {d : ℕ} (μ : Measure (Vec d)) [SFinite μ] (G H : Vec d → Vec d → ℝ)
    (f : Vec d → ℝ)
    (hG : Integrable (fun p : Vec d × Vec d => G p.1 p.2) (μ.prod volume))
    (hH : Integrable (fun p : Vec d × Vec d => H p.1 p.2 * f p.2)
      (μ.prod volume))
    (hpair : ∀ᵐ z ∂μ, (∫ y, G z y) = ∫ y, H z y * f y) :
    (∫ y, ∫ z, G z y ∂μ) = ∫ y, (∫ z, H z y ∂μ) * f y := by
  calc
    (∫ y, ∫ z, G z y ∂μ) = ∫ z, ∫ y, G z y ∂volume ∂μ :=
      (integral_integral_swap hG).symm
    _ = ∫ z, ∫ y, H z y * f y ∂volume ∂μ := integral_congr_ae hpair
    _ = ∫ y, ∫ z, H z y * f y ∂μ := integral_integral_swap hH
    _ = ∫ y, (∫ z, H z y ∂μ) * f y := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [integral_mul_const]

/-- The supplied polynomial Dynkin identity and the explicit generator
commutation identity imply the convolved weak equation for the same law. -/
theorem u6_convolved_weak_of_polynomial_commutation
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (T : ℝ≥0) (r : ℝ) (hr : 0 < r) (f : Vec d → ℝ)
    (hcomm :
      (∫ y, ∫ z, c16NormalizedPolynomialKernel r (d + 1) (z - y) *
        External.Draft.svGenerator (fun _ => ω.1 z)
          (fun _ => physicalDrift ω i lam z) f y
        ∂Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))) =
      ∫ y, (∫ z, physicalGenerator i ω lam
        (fun w => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z
        ∂Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))) * f y) :
    (∫ y, ∫ z, c16NormalizedPolynomialKernel r (d + 1) (z - y) *
      External.Draft.svGenerator (fun _ => ω.1 z)
        (fun _ => physicalDrift ω i lam z) f y
      ∂Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))) =
      ∫ y, ((∫ γ, c16NormalizedPolynomialKernel r (d + 1) (γ T - y) ∂P) -
        c16NormalizedPolynomialKernel r (d + 1) (x - y)) * f y := by
  rw [hcomm]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [u5_supplied_physical_polynomial_occupation_weak_equation
    hd hΛ hω i lam hP r hr y T]

/-- Every measurable finite-dimensional observable has the canonical
expectation under any supplied GMP realization at the same starting point. -/
theorem u6_supplied_gmp_finite_cylinder_integral
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (r : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1)
    (x : Vec d) (I : Finset ℝ≥0) (f : (I → Vec d) → ℝ) (hf : Measurable f) :
    (∫ γ, f (MarkovProcess.ContinuousPath.finsetEvaluation I γ) ∂r.pathLaw x) =
      ∫ v, f v ∂(MarkovProcess.SubMarkovKernelSemigroup.finiteSetKernel
        (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω) I x) := by
  have he := congrArg (fun K => K x)
    (u6_arbitrary_supplied_gmp_canonical_FDD hd ω lam Λ hΛ hω h0 h1 r I)
  rw [Kernel.map_apply _ (MarkovProcess.ContinuousPath.measurable_finsetEvaluation I)] at he
  calc
    _ = ∫ v, f v ∂Measure.map (MarkovProcess.ContinuousPath.finsetEvaluation I)
        (r.pathLaw x) :=
      (integral_map (MarkovProcess.ContinuousPath.measurable_finsetEvaluation I).aemeasurable
        hf.aestronglyMeasurable).symm
    _ = _ := by rw [he]

/-- Fixed-translation occupation comparisons hold simultaneously for almost
every translation at almost every point of the same occupation measure. -/
theorem u6_translation_comparison_ae_swap
    {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (i : Fin d) (lam : ℝ) (μ : Measure (Vec d)) [SFinite μ]
    (κ : Vec d → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hcompare : ∀ y : Vec d, ∀ᵐ z ∂μ,
      physicalGenerator i ω lam (fun w => κ (w - y)) z =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          (fun w => κ (w - y)) z) :
    ∀ᵐ z ∂μ, ∀ᵐ y ∂(volume : Measure (Vec d)),
      physicalGenerator i ω lam (fun w => κ (w - y)) z =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          (fun w => κ (w - y)) z := by
  obtain ⟨hA, _, ⟨Ma, hAb⟩, _, hb, ⟨Mb, hbb⟩⟩ := physical_svHypotheses hΛ hω i lam
  have hcoef : BddCoef (⇑ω.1) (physicalDrift ω i lam) (max Ma Mb) :=
    ⟨fun k j => (hA.matrix_elem k j).measurable,
      fun k => (measurable_pi_apply k).comp hb,
      fun z k j => (hAb z k j).trans (le_max_left _ _),
      fun z k => (hbb z k).trans (le_max_right _ _)⟩
  have hphysical : Measurable (fun p : Vec d × Vec d =>
      physicalGenerator i ω lam (fun w => κ (w - p.1)) p.2) :=
    u6_measurable_physical_generator_translates ω i lam hκ
  have htextbook : Measurable (fun p : Vec d × Vec d =>
      External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
        (fun w => κ (w - p.1)) p.2) := by
    have hm := (c16_bddCoef_measurable_frozen_generator hcoef κ).comp
      (measurable_snd.prodMk (measurable_snd.sub measurable_fst))
    have hm' : Measurable (fun p : Vec d × Vec d =>
        External.Draft.svGenerator (fun _ => ω.1 p.2)
          (fun _ => physicalDrift ω i lam p.2) κ (p.2 - p.1)) := hm
    convert hm' using 1
    funext p
    exact c16_svGenerator_translate (⇑ω.1) (physicalDrift ω i lam) κ p.1 p.2
  have hc : ∀ᵐ y ∂(volume : Measure (Vec d)), ∀ᵐ z ∂μ,
      physicalGenerator i ω lam (fun w => κ (w - y)) z =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          (fun w => κ (w - y)) z := Filter.Eventually.of_forall hcompare
  exact (Measure.ae_ae_comm (p := fun y z =>
    physicalGenerator i ω lam (fun w => κ (w - y)) z =
      External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
        (fun w => κ (w - y)) z) (measurableSet_eq_fun hphysical htextbook)).mp hc


/-- A textbook frozen-generator pairing and fixed-translation comparisons
produce the literal physical pairing for the same spatial measure. -/
theorem u6_physical_spatial_pairing_of_textbook
    {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (i : Fin d) (lam : ℝ) (μ : Measure (Vec d)) [SFinite μ]
    (κ : Vec d → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (f : Vec d → ℝ)
    (hcompare : ∀ y : Vec d, ∀ᵐ z ∂μ,
      physicalGenerator i ω lam (fun w => κ (w - y)) z =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          (fun w => κ (w - y)) z)
    (hpair : ∀ᵐ z ∂μ,
      (∫ y, κ (z - y) * External.Draft.svGenerator (fun _ => ω.1 z)
        (fun _ => physicalDrift ω i lam z) f y) =
      ∫ y, External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
        (fun w => κ (w - y)) z * f y) :
    ∀ᵐ z ∂μ,
      (∫ y, κ (z - y) * External.Draft.svGenerator (fun _ => ω.1 z)
        (fun _ => physicalDrift ω i lam z) f y) =
      ∫ y, physicalGenerator i ω lam (fun w => κ (w - y)) z * f y := by
  filter_upwards [u6_translation_comparison_ae_swap hΛ hω i lam μ κ hκ hcompare,
    hpair] with z hcomp hp
  rw [hp]
  apply integral_congr_ae
  filter_upwards [hcomp] with y hy
  rw [hy]

/-- Two derivatives transfer from a compact smooth test to a smooth kernel. -/
theorem u6_integral_mul_second_fderiv
    {d : ℕ} {a f : Vec d → ℝ}
    (ha : ContDiff ℝ (⊤ : ℕ∞) a) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (v w : Vec d) :
    (∫ y, a y * fderiv ℝ (fun z => fderiv ℝ f z w) y v) =
      ∫ y, fderiv ℝ (fun z => fderiv ℝ a z v) y w * f y := by
  have hfa : ContDiff ℝ 1 (fun z => fderiv ℝ a z v) :=
    ((contDiff_infty_iff_fderiv.mp ha).2.clm_apply contDiff_const).of_le (by simp)
  have hff : ContDiff ℝ 1 (fun z => fderiv ℝ f z w) :=
    ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const).of_le (by simp)
  have hfirst := c16_integral_mul_fderiv (ha.of_le (by simp)) hff
    (hfc.fderiv_apply (𝕜 := ℝ) w) v
  have hsecond := c16_integral_mul_fderiv hfa (hf.of_le (by simp)) hfc w
  rw [hfirst, hsecond, neg_neg]


/-- Differentiating a reflected translate reverses its direction. -/
theorem u6_fderiv_reflected_translate
    {d : ℕ} {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (z y v : Vec d) :
    fderiv ℝ (fun w => κ (z - w)) y v = -fderiv ℝ κ (z - y) v := by
  have h := congrArg (fun L : Vec d →L[ℝ] ℝ => L v)
    ((((hκ.differentiable (by simp)) (z - y)).hasFDerivAt.comp y
      ((hasFDerivAt_id y).const_sub z)).fderiv)
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply, neg_apply,
    ContinuousLinearMap.id_apply, map_neg] using h

/-- Two derivatives of a reflected translate have the original sign. -/
theorem u6_second_fderiv_reflected_translate
    {d : ℕ} {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (z y v w : Vec d) :
    fderiv ℝ (fun x => fderiv ℝ (fun t => κ (z - t)) x v) y w =
      fderiv ℝ (fun x => fderiv ℝ κ x v) (z - y) w := by
  have hk : ContDiff ℝ (⊤ : ℕ∞) (fun x => fderiv ℝ κ x v) :=
    (contDiff_infty_iff_fderiv.mp hκ).2.clm_apply contDiff_const
  have he : (fun x => fderiv ℝ (fun t => κ (z - t)) x v) =
      -(fun x => fderiv ℝ κ (z - x) v) := by
    funext x
    exact u6_fderiv_reflected_translate hκ z x v
  rw [he, fderiv_neg, ContinuousLinearMap.neg_apply,
    u6_fderiv_reflected_translate hk z y w, neg_neg]


/-- A first derivative transfers across a reflected smooth kernel. -/
theorem u6_reflected_integral_first_fderiv
    {d : ℕ} {κ f : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (z v : Vec d) :
    (∫ y, κ (z - y) * fderiv ℝ f y v) =
      ∫ y, fderiv ℝ κ (z - y) v * f y := by
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun y => κ (z - y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  calc
    _ = -∫ y, fderiv ℝ (fun w => κ (z - w)) y v * f y :=
      c16_integral_mul_fderiv (ha.of_le (by simp)) (hf.of_le (by simp)) hfc v
    _ = ∫ y, fderiv ℝ κ (z - y) v * f y := by
      rw [← integral_neg]
      apply integral_congr_ae
      filter_upwards [] with y
      rw [u6_fderiv_reflected_translate hκ z y v]
      ring

/-- Two derivatives transfer across a reflected smooth kernel. -/
theorem u6_reflected_integral_second_fderiv
    {d : ℕ} {κ f : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (z v w : Vec d) :
    (∫ y, κ (z - y) * fderiv ℝ (fun x => fderiv ℝ f x w) y v) =
      ∫ y, fderiv ℝ (fun x => fderiv ℝ κ x v) (z - y) w * f y := by
  have ha : ContDiff ℝ (⊤ : ℕ∞) (fun y => κ (z - y)) :=
    hκ.comp (contDiff_const.sub contDiff_id)
  calc
    _ = ∫ y, fderiv ℝ (fun x => fderiv ℝ (fun t => κ (z - t)) x v) y w * f y :=
      u6_integral_mul_second_fderiv ha hf hfc v w
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [u6_second_fderiv_reflected_translate hκ z y v w]


/-- Mixed directional second derivatives of a smooth real function commute. -/
theorem u6_smooth_second_fderiv_comm
    {d : ℕ} {κ : Vec d → ℝ} (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (x v w : Vec d) :
    fderiv ℝ (fun y => fderiv ℝ κ y v) x w =
      fderiv ℝ (fun y => fderiv ℝ κ y w) x v := by
  have hd : DifferentiableAt ℝ (fderiv ℝ κ) x :=
    ((contDiff_infty_iff_fderiv.mp hκ).2).differentiable (by simp) x
  have hkey : ∀ v w : Vec d,
      fderiv ℝ (fun y => fderiv ℝ κ y v) x w =
        fderiv ℝ (fderiv ℝ κ) x w v := by
    intro v w
    have h := hd.hasFDerivAt.clm_apply (hasFDerivAt_const v x)
    rw [h.fderiv]
    simp
  have hs := (hκ.contDiffAt (x := x)).isSymmSndFDerivAt (by simp)
  rw [hkey v w, hkey w v]
  exact hs w v


/-- A constant drift coefficient passes through the reflected adjoint pairing. -/
theorem u6_reflected_integral_weighted_first
    {d : ℕ} {κ f : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (z v : Vec d) (c : ℝ) :
    (∫ y, κ (z - y) * (c * fderiv ℝ f y v)) =
      ∫ y, (c * fderiv ℝ κ (z - y) v) * f y := by
  calc
    _ = c * ∫ y, κ (z - y) * fderiv ℝ f y v := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = c * ∫ y, fderiv ℝ κ (z - y) v * f y := by
      rw [u6_reflected_integral_first_fderiv hκ hf hfc z v]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring

/-- A constant diffusion coefficient passes through the reflected adjoint pairing. -/
theorem u6_reflected_integral_weighted_second
    {d : ℕ} {κ f : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (z v w : Vec d) (c : ℝ) :
    (∫ y, κ (z - y) *
      (c * fderiv ℝ (fun x => fderiv ℝ f x w) y v)) =
    ∫ y, (c * fderiv ℝ (fun x => fderiv ℝ κ x w) (z - y) v) * f y := by
  calc
    _ = c * ∫ y, κ (z - y) *
        fderiv ℝ (fun x => fderiv ℝ f x w) y v := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = c * ∫ y, fderiv ℝ (fun x => fderiv ℝ κ x v) (z - y) w * f y := by
      rw [u6_reflected_integral_second_fderiv hκ hf hfc z v w]
    _ = c * ∫ y, fderiv ℝ (fun x => fderiv ℝ κ x w) (z - y) v * f y := by
      congr 1
      apply integral_congr_ae
      filter_upwards [] with y
      rw [u6_smooth_second_fderiv_comm hκ (z - y) v w]
    _ = _ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards [] with y
      ring


/-- Assemble the coordinate adjoint identities for a frozen generator. The
integrability assumptions state exactly the four families of summands. -/
theorem u6_frozen_generator_adjoint_of_integrable
    {d : ℕ} {κ f : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (A : Mat d) (b : Vec d) (z : Vec d)
    (hL₂ : ∀ i j : Fin d, Integrable (fun y => κ (z - y) *
      (A i j * fderiv ℝ (fun x => fderiv ℝ f x (unitVector j)) y (unitVector i))))
    (hR₂ : ∀ i j : Fin d, Integrable (fun y =>
      (A i j * fderiv ℝ (fun x => fderiv ℝ κ x (unitVector j)) (z - y)
        (unitVector i)) * f y))
    (hL₁ : ∀ i : Fin d, Integrable (fun y => κ (z - y) *
      (b i * fderiv ℝ f y (unitVector i))))
    (hR₁ : ∀ i : Fin d, Integrable (fun y =>
      (b i * fderiv ℝ κ (z - y) (unitVector i)) * f y)) :
    (∫ y, κ (z - y) * External.Draft.svGenerator (fun _ => A) (fun _ => b) f y) =
      ∫ y, External.Draft.svGenerator (fun _ => A) (fun _ => b) κ (z - y) * f y := by
  let L₂ (i j : Fin d) (y : Vec d) := κ (z - y) *
    (A i j * fderiv ℝ (fun x => fderiv ℝ f x (unitVector j)) y (unitVector i))
  let R₂ (i j : Fin d) (y : Vec d) :=
    (A i j * fderiv ℝ (fun x => fderiv ℝ κ x (unitVector j)) (z - y)
      (unitVector i)) * f y
  let L₁ (i : Fin d) (y : Vec d) := κ (z - y) * (b i * fderiv ℝ f y (unitVector i))
  let R₁ (i : Fin d) (y : Vec d) := (b i * fderiv ℝ κ (z - y) (unitVector i)) * f y
  have hLI (i : Fin d) : Integrable (fun y => ∑ j, L₂ i j y) :=
    integrable_finsetSum _ fun j _ => hL₂ i j
  have hRI (i : Fin d) : Integrable (fun y => ∑ j, R₂ i j y) :=
    integrable_finsetSum _ fun j _ => hR₂ i j
  have hLL : Integrable (fun y => ∑ i, ∑ j, L₂ i j y) :=
    integrable_finsetSum _ fun i _ => hLI i
  have hRR : Integrable (fun y => ∑ i, ∑ j, R₂ i j y) :=
    integrable_finsetSum _ fun i _ => hRI i
  have hLv : Integrable (fun y => ∑ i, L₁ i y) :=
    integrable_finsetSum _ fun i _ => hL₁ i
  have hRv : Integrable (fun y => ∑ i, R₁ i y) :=
    integrable_finsetSum _ fun i _ => hR₁ i
  have hl (y : Vec d) : κ (z - y) *
      External.Draft.svGenerator (fun _ => A) (fun _ => b) f y =
      (1 / 2 : ℝ) * (∑ i, ∑ j, L₂ i j y) + ∑ i, L₁ i y := by
    have ha : κ (z - y) * (∑ i, ∑ j, A i j *
        fderiv ℝ (fun x => fderiv ℝ f x (unitVector j)) y (unitVector i)) =
        ∑ i, ∑ j, L₂ i j y := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rfl
    have hb : κ (z - y) * (∑ i, b i * fderiv ℝ f y (unitVector i)) =
        ∑ i, L₁ i y := by
      simp only [Finset.mul_sum, L₁]
    change κ (z - y) * ((1 / 2 : ℝ) * (∑ i, ∑ j, A i j *
      fderiv ℝ (fun x => fderiv ℝ f x (unitVector j)) y (unitVector i)) +
      ∑ i, b i * fderiv ℝ f y (unitVector i)) = _
    rw [mul_add, mul_left_comm (κ (z - y)) (1 / 2 : ℝ), ha, hb]
  have hr (y : Vec d) :
      External.Draft.svGenerator (fun _ => A) (fun _ => b) κ (z - y) * f y =
      (1 / 2 : ℝ) * (∑ i, ∑ j, R₂ i j y) + ∑ i, R₁ i y := by
    have ha : (∑ i, ∑ j, A i j *
        fderiv ℝ (fun x => fderiv ℝ κ x (unitVector j)) (z - y) (unitVector i)) * f y =
        ∑ i, ∑ j, R₂ i j y := by
      simp only [Finset.sum_mul, R₂]
    have hb : (∑ i, b i * fderiv ℝ κ (z - y) (unitVector i)) * f y =
        ∑ i, R₁ i y := by
      simp only [Finset.sum_mul, R₁]
    change ((1 / 2 : ℝ) * (∑ i, ∑ j, A i j *
      fderiv ℝ (fun x => fderiv ℝ κ x (unitVector j)) (z - y) (unitVector i)) +
      ∑ i, b i * fderiv ℝ κ (z - y) (unitVector i)) * f y = _
    rw [add_mul, mul_assoc, ha, hb]
  calc
    _ = ∫ y, (1 / 2 : ℝ) * (∑ i, ∑ j, L₂ i j y) + ∑ i, L₁ i y :=
      integral_congr_ae (Filter.Eventually.of_forall hl)
    _ = (1 / 2 : ℝ) * (∑ i, ∑ j, ∫ y, L₂ i j y) + ∑ i, ∫ y, L₁ i y := by
      rw [integral_add (hLL.const_mul _) hLv, integral_const_mul,
        integral_finsetSum _ (fun i _ => hLI i),
        integral_finsetSum _ (fun i _ => hL₁ i)]
      have hs : (∑ i, ∫ y, ∑ j, L₂ i j y) =
          ∑ i, ∑ j, ∫ y, L₂ i j y := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_finsetSum _ (fun j _ => hL₂ i j)
      rw [hs]
    _ = (1 / 2 : ℝ) * (∑ i, ∑ j, ∫ y, R₂ i j y) + ∑ i, ∫ y, R₁ i y := by
      congr 1
      · congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro j _
        exact u6_reflected_integral_weighted_second hκ hf hfc z
          (unitVector i) (unitVector j) (A i j)
      · apply Finset.sum_congr rfl
        intro i _
        exact u6_reflected_integral_weighted_first hκ hf hfc z (unitVector i) (b i)
    _ = ∫ y, (1 / 2 : ℝ) * (∑ i, ∑ j, R₂ i j y) + ∑ i, R₁ i y := by
      rw [integral_add (hRR.const_mul _) hRv, integral_const_mul,
        integral_finsetSum _ (fun i _ => hRI i),
        integral_finsetSum _ (fun i _ => hR₁ i)]
      have hs : (∑ i, ∫ y, ∑ j, R₂ i j y) =
          ∑ i, ∑ j, ∫ y, R₂ i j y := by
        apply Finset.sum_congr rfl
        intro i _
        exact integral_finsetSum _ (fun j _ => hR₂ i j)
      rw [hs]
    _ = _ := (integral_congr_ae (Filter.Eventually.of_forall hr)).symm


/-- A smooth kernel and compact smooth test have the frozen-generator adjoint
pairing pointwise, with no integrability hypothesis on the kernel. -/
theorem u6_frozen_generator_adjoint
    {d : ℕ} {κ f : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (A : Mat d) (b : Vec d) (z : Vec d) :
    (∫ y, κ (z - y) * External.Draft.svGenerator (fun _ => A) (fun _ => b) f y) =
      ∫ y, External.Draft.svGenerator (fun _ => A) (fun _ => b) κ (z - y) * f y := by
  have href : Continuous (fun y : Vec d => z - y) := continuous_const.sub continuous_id
  have hfj (j : Fin d) : ContDiff ℝ 1 (fun y => fderiv ℝ f y (unitVector j)) :=
    ((contDiff_infty_iff_fderiv.mp hf).2.clm_apply contDiff_const).of_le (by simp)
  have hκj (j : Fin d) : ContDiff ℝ 1 (fun y => fderiv ℝ κ y (unitVector j)) :=
    ((contDiff_infty_iff_fderiv.mp hκ).2.clm_apply contDiff_const).of_le (by simp)
  have hL₂ (i j : Fin d) : Integrable (fun y => κ (z - y) *
      (A i j * fderiv ℝ (fun x => fderiv ℝ f x (unitVector j)) y (unitVector i))) := by
    have hc : Continuous (fun y => fderiv ℝ
        (fun x => fderiv ℝ f x (unitVector j)) y (unitVector i)) :=
      ((hfj j).continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact ((hκ.continuous.comp href).mul (continuous_const.mul hc)).integrable_of_hasCompactSupport
      (((hfc.fderiv_apply (𝕜 := ℝ) (unitVector j)).fderiv_apply
        (𝕜 := ℝ) (unitVector i)).mul_left.mul_left)
  have hR₂ (i j : Fin d) : Integrable (fun y =>
      (A i j * fderiv ℝ (fun x => fderiv ℝ κ x (unitVector j)) (z - y)
        (unitVector i)) * f y) := by
    have hc : Continuous (fun y => fderiv ℝ
        (fun x => fderiv ℝ κ x (unitVector j)) y (unitVector i)) :=
      ((hκj j).continuous_fderiv (by norm_num)).clm_apply continuous_const
    exact ((continuous_const.mul (hc.comp href)).mul hf.continuous).integrable_of_hasCompactSupport
      hfc.mul_left
  have hL₁ (i : Fin d) : Integrable (fun y => κ (z - y) *
      (b i * fderiv ℝ f y (unitVector i))) :=
    ((hκ.continuous.comp href).mul (continuous_const.mul (hfj i).continuous)).integrable_of_hasCompactSupport
      ((hfc.fderiv_apply (𝕜 := ℝ) (unitVector i)).mul_left.mul_left)
  have hR₁ (i : Fin d) : Integrable (fun y =>
      (b i * fderiv ℝ κ (z - y) (unitVector i)) * f y) :=
    ((continuous_const.mul ((hκj i).continuous.comp href)).mul hf.continuous).integrable_of_hasCompactSupport
      hfc.mul_left
  exact u6_frozen_generator_adjoint_of_integrable hκ hf hfc A b z hL₂ hR₂ hL₁ hR₁

/-- The frozen adjoint can be written using the translated test and the
original coefficient fields evaluated at the frozen point. -/
theorem u6_textbook_generator_spatial_pairing
    {d : ℕ} {κ f : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hfc : HasCompactSupport f) (A : Vec d → Mat d) (b : Vec d → Vec d) (z : Vec d) :
    (∫ y, κ (z - y) * External.Draft.svGenerator (fun _ => A z) (fun _ => b z) f y) =
      ∫ y, External.Draft.svGenerator A b (fun w => κ (w - y)) z * f y := by
  rw [u6_frozen_generator_adjoint hκ hf hfc (A z) (b z) z]
  apply integral_congr_ae
  filter_upwards [] with y
  rw [c16_svGenerator_translate]


/-- Fixed-translation comparisons imply the full spatial pairing for the
same measure, once both test functions have the stated smoothness. -/
theorem u6_physical_spatial_pairing_of_comparison
    {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ) {ω : FieldPair d} (hω : IsRegular Λ ω)
    (i : Fin d) (lam : ℝ) (μ : Measure (Vec d)) [SFinite μ]
    (κ : Vec d → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hcompare : ∀ y : Vec d, ∀ᵐ z ∂μ,
      physicalGenerator i ω lam (fun w => κ (w - y)) z =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          (fun w => κ (w - y)) z) :
    ∀ᵐ z ∂μ,
      (∫ y, κ (z - y) * External.Draft.svGenerator (fun _ => ω.1 z)
        (fun _ => physicalDrift ω i lam z) f y) =
      ∫ y, physicalGenerator i ω lam (fun w => κ (w - y)) z * f y := by
  apply u6_physical_spatial_pairing_of_textbook hΛ hω i lam μ κ hκ f hcompare
  exact Filter.Eventually.of_forall
    (u6_textbook_generator_spatial_pairing hκ hf hfc (⇑ω.1) (physicalDrift ω i lam))

end EinsteinFull
