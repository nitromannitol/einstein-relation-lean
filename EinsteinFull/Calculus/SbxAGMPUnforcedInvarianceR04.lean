import EinsteinFull.Calculus.SbxS5RegularGMPActionR03

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

noncomputable section
namespace EinsteinFull

/-- The supplied origin laws admit a Markov-kernel representative that agrees
with the actual GMP law on a single conull set of environments. -/
theorem s12_exists_unforced_origin_markov_kernel
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (by norm_num) (by norm_num) P) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      ∀ᵐ ω ∂Q.measure, K ω = P (0, ω) := by
  have hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω) := by
    filter_upwards [hP] with ω hω
    obtain ⟨hreg, R, hR⟩ := hω
    letI := R.pathLaw_isMarkovKernel
    rw [originLaw_apply, hR 0]
    infer_instance
  obtain ⟨K, hK, hmark⟩ := Kernel.exists_ae_eq_isMarkovKernel hprob
    (IsProbabilityMeasure.ne_zero Q.measure)
  refine ⟨K, hmark, ?_⟩
  filter_upwards [hK] with ω hω
  simpa only [originLaw_apply] using hω.symm

/-- Annealed invariance for every nonnegative measurable test under the actual
zero-force GMP origin law. -/
theorem s12_gmp_unforced_annealed_invariant
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (by norm_num) (by norm_num) P)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure, K ω = P (0, ω))
    (t : ℝ≥0) (f : FieldPair d → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ ω, ∫⁻ y, f (translate y (reduce ω))
      ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure) =
      ∫⁻ ω, f (reduce ω) ∂Q.measure := by
  obtain ⟨g, hg, hnorm⟩ := u2_exists_normalized_spatial_weight d
  let J : Kernel (Vec d × FieldPair d) (Vec d) :=
    (u2SuppliedSpatialKernel K t).comap (fun p => (p.2, 0))
      (measurable_snd.prodMk measurable_const)
  let J' : Kernel (Vec d × FieldPair d) (Vec d) :=
    (u2SuppliedSpatialKernel K t).comap (fun p => (p.2, p.1))
      (measurable_snd.prodMk measurable_fst)
  have hF : Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      f (translate p.2 (reduce p.1.2)) * g (p.2 + p.1.1)) := by
    apply Measurable.mul
    · exact hf.comp (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (Probability.measurable_reduce.comp
          (measurable_snd.comp measurable_fst))))
    · exact hg.comp (measurable_snd.add (measurable_fst.comp measurable_fst))
  have hF' : Measurable (fun p : (Vec d × FieldPair d) × Vec d =>
      f (translate p.2 (reduce p.1.2)) * g p.2) := by
    apply Measurable.mul
    · exact hf.comp (Probability.continuous_translate.measurable.comp
        (measurable_snd.prodMk (Probability.measurable_reduce.comp
          (measurable_snd.comp measurable_fst))))
    · exact hg.comp measurable_snd
  have hA : Measurable (fun p : Vec d × FieldPair d => ∫⁻ y,
      f (translate y (reduce p.2)) * g (y + p.1) ∂J p) :=
    hF.lintegral_kernel_prod_right
  have hB : Measurable (fun p : Vec d × FieldPair d => ∫⁻ y,
      f (translate y (reduce p.2)) * g y ∂J' p) :=
    hF'.lintegral_kernel_prod_right
  calc
    _ = ∫⁻ ω, ∫⁻ x, ∫⁻ y, f (translate y (reduce ω)) * g (y + x)
        ∂u2SuppliedSpatialKernel K t (ω, 0) ∂volume ∂Q.measure := by
      apply lintegral_congr
      intro ω
      exact (u2_supplied_spatial_origin_weight_average K t ω f g hf hg hnorm).symm
    _ = ∫⁻ x, ∫⁻ ω, ∫⁻ y, f (translate y (reduce ω)) * g (y + x)
        ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure ∂volume :=
      lintegral_lintegral_swap (hA.comp (measurable_snd.prodMk measurable_fst)).aemeasurable
    _ = ∫⁻ x, ∫⁻ ω, ∫⁻ y, f (translate y (reduce ω)) * g y
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂Q.measure ∂volume := by
      apply lintegral_congr
      intro x
      have h := u2_supplied_spatial_kernel_annealed_shift Q K t x f
        (fun y => g (y + x)) hf (show Measurable (fun y => g (y + x)) from
          hg.comp (measurable_id.add measurable_const))
      simpa only [sub_add_cancel] using h
    _ = ∫⁻ ω, ∫⁻ x, ∫⁻ y, f (translate y (reduce ω)) * g y
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂volume ∂Q.measure :=
      (lintegral_lintegral_swap (show AEMeasurable
        (Function.uncurry (fun (ω : FieldPair d) (x : Vec d) => ∫⁻ y,
          f (translate y (reduce ω)) * g y ∂u2SuppliedSpatialKernel K t (ω, x)))
        (Q.measure.prod volume) from
        (hB.comp (measurable_snd.prodMk measurable_fst)).aemeasurable)).symm
    _ = ∫⁻ ω, ∫⁻ y, f (translate y (reduce ω)) * g y ∂volume ∂Q.measure :=
      lintegral_congr_ae (s5_gmp_unforced_spatial_lintegral_volume_invariant
        hd Q P hP K hK t f g hf hg)
    _ = _ := u2_stationary_reduced_orbit_weight_average Q f g hf hg hnorm




/-- The actual unforced GMP environment marginal preserves the reduced law. -/
theorem s12_gmp_unforced_environment_invariant
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (by norm_num) (by norm_num) P)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure, K ω = P (0, ω)) :
    ∀ t : ℝ≥0, c2EnvironmentKernel K t ∘ₘ Q.measure = reducedLaw Q := by
  intro t
  ext s hs
  rw [Measure.bind_apply hs (Kernel.aemeasurable _)]
  change (∫⁻ ω, c2EnvironmentKernel K t ω s ∂Q.measure) = (Q.measure.map reduce) s
  let f : FieldPair d → ℝ≥0∞ := s.indicator 1
  have hf : Measurable f := measurable_const.indicator hs
  have hpoint (ω : FieldPair d) :
      (∫⁻ y, f (translate y (reduce ω)) ∂u2SuppliedSpatialKernel K t (ω, 0)) =
        c2EnvironmentKernel K t ω s := by
    rw [← lintegral_map hf (show Measurable (fun y : Vec d => translate y (reduce ω)) from
      Probability.continuous_translate.measurable.comp (measurable_id.prodMk measurable_const)),
      ← u2_environment_kernel_eq_supplied_spatial_origin]
    simpa only [f] using (lintegral_indicator_one (μ := c2EnvironmentKernel K t ω) hs)
  calc
    _ = ∫⁻ ω, ∫⁻ y, f (translate y (reduce ω))
        ∂u2SuppliedSpatialKernel K t (ω, 0) ∂Q.measure := by
      apply lintegral_congr
      intro ω
      exact (hpoint ω).symm
    _ = ∫⁻ ω, f (reduce ω) ∂Q.measure :=
      s12_gmp_unforced_annealed_invariant hd Q P hP K hK t f hf
    _ = _ := by
      rw [← lintegral_map hf Probability.measurable_reduce]
      simpa only [f] using (lintegral_indicator_one (μ := Q.measure.map reduce) hs)




end EinsteinFull
