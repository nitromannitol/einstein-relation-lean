import EinsteinFull.Calculus.U6GMPSmoothRealization
import EinsteinFull.Calculus.U6PhysicalSameKRealization
import EinsteinFull.Calculus.U6PhysicalPathMoments
import EinsteinFull.Calculus.C16PhysicalMPExistence

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull

/-- One measurable physical solution kernel agrees with the full GMP realization
at every smooth regular environment outside a single null set. The physical
martingale problem itself holds almost surely without smoothness. -/
theorem u6_physical_origin_kernel_with_smooth_gmp_identification
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (hΛ : 1 ≤ Λ)
    (Q : EnvironmentLaw d Λ r) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      (∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
        (physicalGenerator (firstCoordinateIndex hd) ω lam) 0 (K ω)) ∧
      (∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ ω,
        ∀ hSmooth : IsSmoothFieldPair ω,
          ∃ R : GantertFixedEnvironmentRealization hd Λ hΛ ω hω lam h0 h1,
            K ω = R.pathLaw 0) := by
  obtain ⟨PX, _PY, hX, _hY, _hclock⟩ :=
    c16_physical_reduced_mp_exists_with_inverse_clock d hd Λ r Q
      (firstCoordinateIndex hd) lam
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw PX ω) :=
    hX.mono fun _ h => h.1
  obtain ⟨K, hK, hmarkov⟩ := Kernel.exists_ae_eq_isMarkovKernel hprob
    (IsProbabilityMeasure.ne_zero Q.measure)
  refine ⟨K, hmarkov, ?_, ?_⟩
  · filter_upwards [hK, hX] with ω he hP
    rw [← he]
    exact hP
  · filter_upwards [hK, hX] with ω he hP
    intro hω hSmooth
    refine ⟨u6GmpSmoothFixedEnvironmentRealization
      hd hΛ ω hω hSmooth lam h0 h1, ?_⟩
    letI : IsMarkovKernel (Blueprint.gmpPhysicalPathLaw hd ω lam Λ hΛ hω hSmooth) :=
      Blueprint.gmpPhysicalPathLaw_isMarkovKernel hd ω lam Λ hΛ hω hSmooth
    have hEq := c4_physical_supplied_law_eq_gmp_realization_of_smooth
      hd ω lam Λ hΛ hω hSmooth
      (Blueprint.gmpPhysicalPathLaw hd ω lam Λ hΛ hω hSmooth)
      (Blueprint.gmpPhysicalPathLaw_spec hd ω lam Λ hΛ hω hSmooth).2
      0 (PX (0, ω)) hP
    exact he.symm.trans (hEq.trans rfl)

#print axioms u6_physical_origin_kernel_with_smooth_gmp_identification


/-- Generator commutation for the same physical solution yields absolute
continuity of its positive-time occupation measure. -/
theorem u6_occupation_ac_of_polynomial_commutation
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (hcomm : ∀ (T : ℝ≥0) (r : ℝ), 0 < r → ∀ (f : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      (∫ y, ∫ z, c16NormalizedPolynomialKernel r (d + 1) (z - y) *
        External.Draft.svGenerator (fun _ => ω.1 z)
          (fun _ => physicalDrift ω i lam z) f y
        ∂Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))) =
      ∫ y, (∫ z, physicalGenerator i ω lam
        (fun w => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z
        ∂Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))) * f y) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  let : IsProbabilityMeasure P := hP.1
  apply u6_occupation_ac_of_energy hd
  intro T
  apply u6_literal_physical_finite_occupation_energy_of_convolved_weak
    hd hΛ hω i lam hP T
  intro r hr f hf hfc
  exact u6_convolved_weak_of_polynomial_commutation hd hΛ hω i lam hP T r hr f
    (hcomm T r hr f hf hfc)


/-- Bounded derivatives of a smooth kernel give integrability of its literal
physical generator paired with a compactly supported test. -/
theorem u6_integrable_physical_generator_translates
    {d : ℕ} {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {κ : Vec d → ℝ}
    (hκ : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hb : ∃ B : ℝ, ∀ k ≤ 2, ∀ z : Vec d, ‖iteratedFDeriv ℝ k κ z‖ ≤ B)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    Integrable (fun p : Vec d × Vec d =>
      physicalGenerator i ω lam (fun w => κ (w - p.2)) p.1 * f p.2)
      (μ.prod volume) := by
  obtain ⟨B, hB⟩ := u6_physical_generator_uniform_translates hΛ hω i lam hκ hb
  have hm : Measurable (Function.uncurry (fun z y =>
      physicalGenerator i ω lam (fun w => κ (w - y)) z)) := by
    have htrans : Measurable (fun p : Vec d × Vec d =>
        physicalGenerator i ω lam (fun w => κ (w - p.1)) p.2) :=
      u6_measurable_physical_generator_translates ω i lam hκ
    exact htrans.comp measurable_swap
  exact u6_integrable_bounded_pairing_mul_test μ hm hB hf.continuous
    (hf.continuous.integrable_of_hasCompactSupport hfc)

/-- The literal generator of translated polynomial kernels is integrable
against any finite spatial measure and a smooth compactly supported test. -/
theorem u6_integrable_polynomial_physical_generator
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f) :
    Integrable (fun p : Vec d × Vec d =>
      physicalGenerator i ω lam
        (fun w => c16NormalizedPolynomialKernel r (d + 1) (w - p.2)) p.1 * f p.2)
      (μ.prod volume) := by
  have hdm : (d : ℝ) < 2 * ((d + 1 : ℕ) : ℝ) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast
    linarith
  have hκ : ContDiff ℝ (⊤ : ℕ∞) (c16NormalizedPolynomialKernel r (d + 1)) :=
    (c16_normalized_polynomial_kernel_properties (d := d)
    hr (d + 1) hdm).2.1
  have hb : ∃ B : ℝ, ∀ k ≤ 2, ∀ z : Vec d,
      ‖iteratedFDeriv ℝ k (c16NormalizedPolynomialKernel r (d + 1)) z‖ ≤ B :=
    u5_normalized_polynomial_unshifted_iterated_bounded (d := d) hr
  exact u6_integrable_physical_generator_translates hΛ hω i lam μ hκ hb f hf hfc


/-- A spatial generator pairing under a finite measure implies polynomial
commutation, with both product-integrability obligations discharged. -/
theorem u6_polynomial_commutation_of_spatial_pairing
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    (μ : Measure (Vec d)) [IsFiniteMeasure μ] {r : ℝ} (hr : 0 < r)
    (f : Vec d → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hfc : HasCompactSupport f)
    (hpair : ∀ᵐ z ∂μ,
      (∫ y, c16NormalizedPolynomialKernel r (d + 1) (z - y) *
        External.Draft.svGenerator (fun _ => ω.1 z)
          (fun _ => physicalDrift ω i lam z) f y) =
      ∫ y, physicalGenerator i ω lam
        (fun w => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z * f y) :
    (∫ y, ∫ z, c16NormalizedPolynomialKernel r (d + 1) (z - y) *
      External.Draft.svGenerator (fun _ => ω.1 z)
        (fun _ => physicalDrift ω i lam z) f y ∂μ) =
    ∫ y, (∫ z, physicalGenerator i ω lam
      (fun w => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z ∂μ) * f y := by
  exact u6_commutation_of_spatial_pairing μ
    (fun z y => c16NormalizedPolynomialKernel r (d + 1) (z - y) *
      External.Draft.svGenerator (fun _ => ω.1 z)
        (fun _ => physicalDrift ω i lam z) f y)
    (fun z y => physicalGenerator i ω lam
      (fun w => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z) f
    (u6_integrable_polynomial_frozen_generator hd hΛ hω i lam μ hr f hf hfc)
    (u6_integrable_polynomial_physical_generator hd hΛ hω i lam μ hr f hf hfc)
    hpair


/-- Spatial pairing on the finite occupation of the supplied law implies
absolute continuity of its positive-time occupation measure. -/
theorem u6_occupation_ac_of_polynomial_spatial_pairing
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (hpair : ∀ (T : ℝ≥0) (r : ℝ), 0 < r → ∀ (f : Vec d → ℝ),
      ContDiff ℝ (⊤ : ℕ∞) f → HasCompactSupport f →
      ∀ᵐ z ∂(Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))),
        (∫ y, c16NormalizedPolynomialKernel r (d + 1) (z - y) *
          External.Draft.svGenerator (fun _ => ω.1 z)
            (fun _ => physicalDrift ω i lam z) f y) =
        ∫ y, physicalGenerator i ω lam
          (fun w => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z * f y) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  let : IsProbabilityMeasure P := hP.1
  apply u6_occupation_ac_of_polynomial_commutation hd hΛ hω i lam hP
  intro T r hr f hf hfc
  let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  let : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by infer_instance
  let : IsFiniteMeasure μ := Measure.isFiniteMeasure_map _ _
  exact u6_polynomial_commutation_of_spatial_pairing hd hΛ hω i lam μ hr f hf hfc
    (hpair T r hr f hf hfc)

/-- Fixed-translation generator comparisons on the same finite occupation
measure imply absolute continuity of the positive-time occupation measure. -/
theorem u6_occupation_ac_of_polynomial_translation_comparison
    {d : ℕ} (hd : 2 ≤ d) {Λ : ℝ} (hΛ : 0 < Λ)
    {ω : FieldPair d} (hω : IsRegular Λ ω) (i : Fin d) (lam : ℝ)
    {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (physicalGenerator i ω lam) x P)
    (hcompare : ∀ (T : ℝ≥0) (r : ℝ), 0 < r → ∀ y : Vec d,
      ∀ᵐ z ∂(Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))),
        physicalGenerator i ω lam
          (fun w => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z =
        External.Draft.svGenerator (⇑ω.1) (physicalDrift ω i lam)
          (fun w => c16NormalizedPolynomialKernel r (d + 1) (w - y)) z) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  let : IsProbabilityMeasure P := hP.1
  apply u6_occupation_ac_of_polynomial_spatial_pairing hd hΛ hω i lam hP
  intro T r hr f hf hfc
  let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
  let : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) := by infer_instance
  let : IsFiniteMeasure μ := Measure.isFiniteMeasure_map _ _
  have hdm : (d : ℝ) < 2 * ((d + 1 : ℕ) : ℝ) := by
    have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
    push_cast
    linarith
  have hκ : ContDiff ℝ (⊤ : ℕ∞) (c16NormalizedPolynomialKernel r (d + 1)) :=
    (c16_normalized_polynomial_kernel_properties (d := d) hr (d + 1) hdm).2.1
  exact u6_physical_spatial_pairing_of_comparison hΛ hω i lam μ
    (c16NormalizedPolynomialKernel r (d + 1)) hκ f hf hfc (hcompare T r hr)


end EinsteinFull
