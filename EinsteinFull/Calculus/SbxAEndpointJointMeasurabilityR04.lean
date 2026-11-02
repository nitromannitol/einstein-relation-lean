import EinsteinFull.Calculus.SbxS5RegularGMPActionR03

/-! Joint measurability for the actual supplied GMP endpoint action. -/

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull

/-- The literal GMP endpoint action has a jointly strongly measurable version,
valid simultaneously at all times on one conull set of environments. -/
theorem s7_gmp_endpoint_jointly_strongly_measurable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (f : FieldPair d → E) (hf : StronglyMeasurable f) :
    ∃ H : ℝ × FieldPair d → E, StronglyMeasurable H ∧
      ∀ᵐ ω ∂Q.measure, ∀ t : ℝ,
        H (t, ω) = ∫ γ : Path d,
          f (translate (γ t.toNNReal) (reduce ω)) ∂P (0, ω) := by
  obtain ⟨K, hmarkov, hK⟩ := s5_gmp_origin_markov_version hd Q mu h0 h1 P hP
  letI : IsMarkovKernel K := hmarkov
  let K' : Kernel (ℝ × FieldPair d) (Path d) := K.comap Prod.snd measurable_snd
  let endpoint : (ℝ × FieldPair d) × Path d → FieldPair d := fun p =>
    translate (p.2 p.1.1.toNNReal) (reduce p.1.2)
  have hE : Measurable endpoint := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_snd.prodMk
        (continuous_real_toNNReal.comp (continuous_fst.comp continuous_fst)))).prodMk
        (Probability.continuous_reduce.comp (continuous_snd.comp continuous_fst)))).measurable
  let H : ℝ × FieldPair d → E := fun p => ∫ γ, f (endpoint (p, γ)) ∂K' p
  have hH : StronglyMeasurable H := (hf.comp_measurable hE).integral_kernel_prod_right'
  refine ⟨H, hH, ?_⟩
  filter_upwards [hK] with ω hω
  intro t
  change (∫ γ, f (translate (γ t.toNNReal) (reduce ω)) ∂K ω) = _
  rw [hω]

/-- The conclusion applies to the canonical representative of each reduced-law
L² class, without an assertion of endpoint integrability. -/
theorem s7_gmp_endpoint_L2_jointly_strongly_measurable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    ∃ H : ℝ × FieldPair d → ℂ, StronglyMeasurable H ∧
      ∀ᵐ ω ∂Q.measure, ∀ t : ℝ,
        H (t, ω) = ∫ γ : Path d,
          f (translate (γ t.toNNReal) (reduce ω)) ∂P (0, ω) :=
  s7_gmp_endpoint_jointly_strongly_measurable hd Q mu h0 h1 P hP f
    (Lp.stronglyMeasurable f)

/-- On any finite time interval, a measurable GMP endpoint representative is
almost everywhere strongly measurable for the time-environment product measure. -/
theorem s7_gmp_endpoint_L2_finite_interval_measurable
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (f : Lp ℂ 2 (reducedLaw Q)) (a b : ℝ) :
    ∃ H : ℝ × FieldPair d → ℂ,
      AEStronglyMeasurable H ((volume.restrict (Set.Ioc a b)).prod Q.measure) ∧
      ∀ᵐ ω ∂Q.measure, ∀ t : ℝ,
        H (t, ω) = ∫ γ : Path d,
          f (translate (γ t.toNNReal) (reduce ω)) ∂P (0, ω) := by
  obtain ⟨H, hH, heq⟩ := s7_gmp_endpoint_L2_jointly_strongly_measurable
    hd Q mu h0 h1 P hP f
  exact ⟨H, hH.aestronglyMeasurable, heq⟩

/-- For bounded measurable data the endpoint action is integrable on every
finite time interval and admits the Fubini interchange used by Dynkin's formula. -/
theorem s7_gmp_bounded_endpoint_fubini
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (mu : ℝ) (h0 : 0 ≤ mu) (h1 : mu ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q mu h0 h1 P)
    (f : FieldPair d → E) (hf : StronglyMeasurable f)
    (C : ℝ) (hC : ∀ ρ, ‖f ρ‖ ≤ C) (a b : ℝ) :
    ∃ H : ℝ × FieldPair d → E,
      Integrable H ((volume.restrict (Set.Ioc a b)).prod Q.measure) ∧
      (∀ᵐ ω ∂Q.measure, ∀ t : ℝ,
        H (t, ω) = ∫ γ : Path d,
          f (translate (γ t.toNNReal) (reduce ω)) ∂P (0, ω)) ∧
      (∫ t in Set.Ioc a b, ∫ ω,
        (∫ γ : Path d, f (translate (γ t.toNNReal) (reduce ω)) ∂P (0, ω))
          ∂Q.measure) =
      ∫ ω, (∫ t in Set.Ioc a b,
        (∫ γ : Path d, f (translate (γ t.toNNReal) (reduce ω)) ∂P (0, ω))) ∂Q.measure := by
  obtain ⟨K, hmarkov, hK⟩ := s5_gmp_origin_markov_version hd Q mu h0 h1 P hP
  letI : IsMarkovKernel K := hmarkov
  let K' : Kernel (ℝ × FieldPair d) (Path d) := K.comap Prod.snd measurable_snd
  let endpoint : (ℝ × FieldPair d) × Path d → FieldPair d := fun p =>
    translate (p.2 p.1.1.toNNReal) (reduce p.1.2)
  have hE : Measurable endpoint := by
    exact (Probability.continuous_translate.comp
      ((continuous_eval.comp (continuous_snd.prodMk
        (continuous_real_toNNReal.comp (continuous_fst.comp continuous_fst)))).prodMk
        (Probability.continuous_reduce.comp (continuous_snd.comp continuous_fst)))).measurable
  let H : ℝ × FieldPair d → E := fun p => ∫ γ, f (endpoint (p, γ)) ∂K' p
  have hH : StronglyMeasurable H := (hf.comp_measurable hE).integral_kernel_prod_right'
  have hbound (p : ℝ × FieldPair d) : ‖H p‖ ≤ C := by
    have hb := norm_integral_le_of_norm_le_const
      (μ := K' p) (f := fun γ => f (endpoint (p, γ)))
      (Filter.Eventually.of_forall (fun γ => hC (endpoint (p, γ))))
    simpa using hb
  letI : IsFiniteMeasure (volume.restrict (Set.Ioc a b)) :=
    ⟨by rw [Measure.restrict_apply_univ]; simp⟩
  have hint : Integrable H ((volume.restrict (Set.Ioc a b)).prod Q.measure) :=
    (integrable_const C).mono' hH.aestronglyMeasurable
      (Filter.Eventually.of_forall hbound)
  have heq : ∀ᵐ ω ∂Q.measure, ∀ t : ℝ,
      H (t, ω) = ∫ γ : Path d,
        f (translate (γ t.toNNReal) (reduce ω)) ∂P (0, ω) := by
    filter_upwards [hK] with ω hω
    intro t
    change (∫ γ, f (translate (γ t.toNNReal) (reduce ω)) ∂K ω) = _
    rw [hω]
  refine ⟨H, hint, heq, ?_⟩
  calc
    _ = ∫ t in Set.Ioc a b, ∫ ω, H (t, ω) ∂Q.measure := by
      apply integral_congr_ae
      filter_upwards [] with t
      apply integral_congr_ae
      filter_upwards [heq] with ω hω
      exact (hω t).symm
    _ = ∫ ω, (∫ t in Set.Ioc a b, H (t, ω)) ∂Q.measure :=
      integral_integral_swap hint
    _ = _ := by
      apply integral_congr_ae
      filter_upwards [heq] with ω hω
      apply integral_congr_ae
      filter_upwards [] with t
      exact hω t

end EinsteinFull
