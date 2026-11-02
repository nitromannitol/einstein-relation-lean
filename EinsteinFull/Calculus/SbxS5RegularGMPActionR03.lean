import EinsteinFull.Calculus.SbxS6SuppliedKernelUniquenessR01
import EinsteinFull.Calculus.U3RealForceBoundedTests
import EinsteinFull.Calculus.U6BoundedPhysicalResolvent
import EinsteinFull.Calculus.U2RegularKernelCovariance

/-! The horizontal-test generator identity for the supplied regular GMP law. -/

open EinsteinRelation MeasureTheory ProbabilityTheory
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull

/-- The supplied GMP law has the regular reduced spatial semigroup as its
endpoint marginal at every start and time. -/
theorem s5_gmp_regular_marginals
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω, ∀ x : Vec d, ∀ t : ℝ≥0,
      (P (x, ω)).map (pathPosition t) =
        u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) lam
          (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
          (flatReducedEnvironment_regular Q.ellipticity_parameter hω) t x := by
  filter_upwards [hP] with ω hω hreg x t
  obtain ⟨hflat, R, hR⟩ := hω
  rw [hR x, R.pathLaw_endpoint,
    u6_arbitrary_supplied_gmp_transition_eq hd (zeroPotentialReducedPair ω) lam
      (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
      hflat h0 h1 R t]
  rfl

/-- The supplied origin laws admit a Markov kernel version, agreeing almost
everywhere with the original GMP law. -/
theorem s5_gmp_origin_markov_version
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∃ K : Kernel (FieldPair d) (Path d), IsMarkovKernel K ∧
      ∀ᵐ ω ∂Q.measure, K ω = P (0, ω) := by
  classical
  let K₀ : Kernel (FieldPair d) (Path d) :=
    P.comap (fun ω => (0, ω)) (measurable_const.prodMk measurable_id)
  let S : Set (FieldPair d) := {ω | K₀ ω Set.univ = 1}
  have hS : MeasurableSet S := measurableSet_eq_fun (K₀.measurable_coe MeasurableSet.univ) measurable_const
  let K : Kernel (FieldPair d) (Path d) :=
    Kernel.piecewise hS K₀ (Kernel.const _ (Measure.dirac (0 : Path d)))
  have hmark : IsMarkovKernel K := by
    refine ⟨fun ω => ⟨?_⟩⟩
    by_cases hω : ω ∈ S
    · have hmass : K₀ ω Set.univ = 1 := hω
      simpa [K, Kernel.piecewise_apply, hω] using hmass
    · simp [K, Kernel.piecewise_apply, hω]
  refine ⟨K, hmark, ?_⟩
  filter_upwards [hP] with ω hω
  obtain ⟨hreg, R, hR⟩ := hω
  letI : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  have hp : IsProbabilityMeasure (P (0, ω)) := by rw [hR 0]; infer_instance
  have hωS : ω ∈ S := by
    change P (0, ω) Set.univ = 1
    exact hp.measure_univ
  simp [K, Kernel.piecewise_apply, hωS, K₀]

/-- The spatial kernel built from a Markov version of the supplied GMP origin
law agrees with the regular semigroup along almost every spatial orbit. -/
theorem s5_gmp_spatial_kernel_regular_orbit_ae
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure, K ω = P (0, ω)) :
    ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω, ∀ᵐ x : Vec d ∂volume, ∀ t : ℝ≥0,
      u2SuppliedSpatialKernel K t (ω, x) =
        u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) lam
          (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
          (flatReducedEnvironment_regular Q.ellipticity_parameter hω) t x := by
  have hbase : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω, ∀ t : ℝ≥0,
      (K ω).map (pathPosition t) =
        u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) lam
          (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
          (flatReducedEnvironment_regular Q.ellipticity_parameter hω) t 0 := by
    filter_upwards [s5_gmp_regular_marginals hd Q lam h0 h1 P hP, hK] with ω hmarg he hω t
    rw [he]
    exact hmarg hω 0 t
  have horbit := u2_stationary_full_event_spatial_orbit Q hbase
  filter_upwards [horbit] with ω hωshift hω
  filter_upwards [hωshift] with x hx t
  have hregshift : IsRegular Λ₀ (translate x ω) :=
    (ActualImageLpStateTransport.isRegular_translate_iff x ω).mpr hω
  have hflat := flatReducedEnvironment_regular Q.ellipticity_parameter hω
  obtain ⟨hflatshift, hcov⟩ := u2_regular_signed_kernel_translation_covariance
    hd (flatReducedEnvironment ω) lam (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) hflat x
  have hmarg : (K (translate x ω)).map (pathPosition t) =
      u2RegularC0KernelSemigroup hd (translate x (flatReducedEnvironment ω)) lam
        (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        hflatshift t 0 := by
    simpa only [flatReducedEnvironment_translate] using hx hregshift t
  rw [u2_supplied_spatial_kernel_apply]
  have hmap : (K (translate x ω)).map (fun γ => x + γ t) =
      ((K (translate x ω)).map (pathPosition t)).map (fun y : Vec d => x + y) := by
    rw [Measure.map_map (show Measurable (fun y : Vec d => x + y) from
      measurable_const.add measurable_id) (measurable_pathPosition t)]
    rfl
  rw [hmap, hmarg, hcov t 0]
  simp only [zero_add]
  rw [Measure.map_map (show Measurable (fun y : Vec d => x + y) from
    measurable_const.add measurable_id)
    (show Measurable (fun y : Vec d => y - x) from measurable_id.sub measurable_const)]
  simp [Function.comp_def, sub_eq_add_neg]

/-- The unforced spatial kernel constructed from the actual GMP origin law
preserves Lebesgue measure on almost every environment. -/
theorem s5_gmp_unforced_spatial_volume_invariant
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (le_refl 0) (by norm_num) P)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure, K ω = P (0, ω)) :
    ∀ᵐ ω ∂Q.measure, ∀ t : ℝ≥0,
      ((u2SuppliedSpatialKernel K t).comap (fun x => (ω, x))
        (measurable_const.prodMk measurable_id)) ∘ₘ (volume : Measure (Vec d)) = volume := by
  have horbit := s5_gmp_spatial_kernel_regular_orbit_ae hd Q 0 (le_refl 0) (by norm_num) P hP K hK
  filter_upwards [horbit, Q.regular] with ω horbitω hω t
  let hflat := flatReducedEnvironment_regular Q.ellipticity_parameter hω
  have heq : ∀ᵐ x : Vec d ∂volume,
      (u2SuppliedSpatialKernel K t).comap (fun x => (ω, x))
          (measurable_const.prodMk measurable_id) x =
        u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) 0
          (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
          hflat t x := (horbitω hω).mono fun x hx => hx t
  calc
    _ = (u2RegularC0KernelSemigroup hd (flatReducedEnvironment ω) 0
        (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter)
        hflat t) ∘ₘ (volume : Measure (Vec d)) := Measure.comp_congr heq
    _ = volume := u2_unforced_reduced_kernel_volume_invariant hd ω
        (sourceReducedBound Λ₀) (one_le_sourceReducedBound Q.ellipticity_parameter) hflat t

/-- Spatial volume invariance evaluated against nonnegative measurable tests. -/
theorem s5_gmp_unforced_spatial_lintegral_volume_invariant
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q 0 (le_refl 0) (by norm_num) P)
    (K : Kernel (FieldPair d) (Path d)) [IsMarkovKernel K]
    (hK : ∀ᵐ ω ∂Q.measure, K ω = P (0, ω))
    (t : ℝ≥0) (f : FieldPair d → ℝ≥0∞) (g : Vec d → ℝ≥0∞)
    (hf : Measurable f) (hg : Measurable g) :
    ∀ᵐ ω ∂Q.measure,
      (∫⁻ x, ∫⁻ y, f (translate y (reduce ω)) * g y
        ∂u2SuppliedSpatialKernel K t (ω, x) ∂volume) =
      ∫⁻ y, f (translate y (reduce ω)) * g y ∂volume := by
  filter_upwards [s5_gmp_unforced_spatial_volume_invariant hd Q P hP K hK] with ω hω
  let J : Kernel (Vec d) (Vec d) :=
    (u2SuppliedSpatialKernel K t).comap (fun x => (ω, x))
      (measurable_const.prodMk measurable_id)
  have hF : Measurable (fun y : Vec d => f (translate y (reduce ω)) * g y) :=
    (hf.comp (Probability.continuous_translate.measurable.comp
      (measurable_id.prodMk measurable_const))).mul hg
  change (∫⁻ x, ∫⁻ y, f (translate y (reduce ω)) * g y ∂J x ∂volume) = _
  rw [← Measure.lintegral_bind J.aemeasurable hF.aemeasurable, hω t]

/-- The supplied GMP realization satisfies the textbook equation at every start.
The positive-time density supplies the occupation absolute continuity needed to
compare the divergence and textbook generators. -/
theorem s5_gmp_textbook_at_every_start
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) lam)) x (P (x, ω)) := by
  filter_upwards [hP] with ω hω
  obtain ⟨hreg, R, hR⟩ := hω
  letI : IsMarkovKernel R.pathLaw := R.pathLaw_isMarkovKernel
  have hflatpos : 0 < sourceReducedBound Λ₀ :=
    lt_of_lt_of_le zero_lt_one (one_le_sourceReducedBound Q.ellipticity_parameter)
  intro x
  have hmarg : ∀ t : ℝ≥0, 0 < t →
      (R.pathLaw x).map (pathPosition t) ≪ (volume : Measure (Vec d)) := by
    intro t ht
    rw [R.pathLaw_endpoint, R.transitionKernel_eq_heatKernel t ht x]
    exact withDensity_absolutelyContinuous _ _
  have hphys := foundation_arbitrary_supplied_gmp_physical_MP hd (sourceReducedBound Λ₀)
    (one_le_sourceReducedBound Q.ellipticity_parameter) (zeroPotentialReducedPair ω)
    hreg lam h0 h1 R x
  have htext := c4_textbook_solves_of_physical_and_averaged_occupation
    hflatpos hreg (firstCoordinateIndex hd) lam hphys
    (u2_averaged_occupation_ac_of_marginals (R.pathLaw x) hmarg)
  rw [hR x]
  have hc : (⇑(zeroPotentialReducedPair ω).1 : Vec d → Mat d) = reducedCoefficient ω := rfl
  have hb : physicalDrift (zeroPotentialReducedPair ω) (firstCoordinateIndex hd) lam =
      forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) lam := by
    have hc' : reducedCoefficient (zeroPotentialReducedPair ω) = reducedCoefficient ω := by
      funext y
      exact reducedCoefficient_zeroPotentialReducedPair ω y
    funext y j
    simp only [physicalDrift, hc']
    simp [clockDensity, zeroPotentialReducedPair]
  rwa [hc, hb] at htext

/-- Dynkin's formula on horizontal tests for the actual reduced GMP law,
with no uniqueness assumption for arbitrary martingale-problem solutions. -/
theorem s5_gmp_horizontal_generator_dynkin
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (F : FieldPair d → ℝ) (hF : IsHorizontalTest F) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      Integrable (fun γ : Path d => ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd lam F (translate (γ u.toNNReal) (reduce ω))) (P (0, ω)) ∧
      (∫ γ : Path d, (∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
        envGenerator hd lam F (translate (γ u.toNNReal) (reduce ω))) ∂P (0, ω)) =
        (∫ γ : Path d, F (translate (γ T) (reduce ω)) ∂P (0, ω)) - F (reduce ω) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, s5_gmp_textbook_at_every_start hd Q lam h0 h1 P hP] with ω hω htext
  have h := u3_reduced_signed_bounded_C2_dynkin hΛ hω (firstCoordinateIndex hd) lam
    (htext 0) (orbit F (reduce ω)) (contDiff_two_of_top (hF.2.1 (reduce ω)))
    (c17_horizontal_test_bounded_C2 F hF (reduce ω)) T
  have hs : ∀ x j k, (reduce ω).1 x j k = (reduce ω).1 x k j := by
    intro x j k
    have he := congrArg (fun M : Mat d => M j k) (reducedCoefficient_symm hω x)
    exact he.symm
  have he (x : Vec d) : envGenerator hd lam F (translate x (reduce ω)) =
      External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) (firstCoordinateIndex hd) lam)
          (orbit F (reduce ω)) x :=
    u3_signed_envGenerator_eq_svGenerator hd (reduce ω) F lam hs x
  simp_rw [← he] at h
  simpa only [orbit, translate_zero] using h

/-- The supplied GMP action obeys the integral generator equation on
horizontal tests. -/
theorem s5_gmp_horizontal_generator_integral_equation
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (P : QuenchedPathLaws d)
    (hP : IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h0 h1 P)
    (F : FieldPair d → ℝ) (hF : IsHorizontalTest F) (T : ℝ≥0) :
    ∀ᵐ ω ∂Q.measure,
      (∫ γ : Path d, F (translate (γ T) (reduce ω)) ∂P (0, ω)) - F (reduce ω) =
        ∫ u in Set.Ioc (0 : ℝ) (T : ℝ),
          ∫ γ : Path d, envGenerator hd lam F (translate (γ u.toNNReal) (reduce ω)) ∂P (0, ω) := by
  obtain ⟨B, hB0, hB⟩ := exists_abs_envGenerator_le hd lam hF (Entropy.sourceReducedBound_pos' Λ₀)
  let Φ : FieldPair d → Path d → ℝ → ℝ := fun ω γ u =>
    envGenerator hd lam F (translate (γ u.toNNReal) (reduce ω))
  have hΦB : ∀ ω, IsRegular Λ₀ ω → ∀ γ u, |Φ ω γ u| ≤ B := fun ω hω γ u =>
    hB (zeroPotentialReducedPair ω) (reduce ω)
      (isRegular_zeroPotentialReducedPair Q.ellipticity_parameter hω) rfl _
  have heval : Continuous (fun p : (FieldPair d × ℝ) × Path d => p.2 p.1.2.toNNReal) :=
    continuous_eval.comp (continuous_snd.prodMk
      (continuous_real_toNNReal.comp (continuous_snd.comp continuous_fst)))
  have henv : Measurable (fun p : (FieldPair d × ℝ) × Path d =>
      translate (p.2 p.1.2.toNNReal) (reduce p.1.1)) :=
    (Probability.continuous_translate.comp
      (heval.prodMk (Probability.continuous_reduce.comp
        (continuous_fst.comp continuous_fst)))).measurable
  have hΦm : Measurable (fun p : (FieldPair d × ℝ) × Path d => Φ p.1.1 p.2 p.1.2) :=
    (measurable_envGenerator hd lam hF).comp henv
  filter_upwards [Q.regular, s5_gmp_textbook_at_every_start hd Q lam h0 h1 P hP,
    s5_gmp_horizontal_generator_dynkin hd Q lam h0 h1 P hP F hF T]
    with ω hω htext hdyn
  letI : IsProbabilityMeasure (P (0, ω)) := (htext 0).1
  have hfin : IsFiniteMeasure (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))) :=
    ⟨by rw [Measure.restrict_apply_univ]; simp⟩
  have hint : Integrable (Function.uncurry fun (γ : Path d) (u : ℝ) => Φ ω γ u)
      ((P (0, ω)).prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))) := by
    refine (integrable_const B).mono'
      (hΦm.comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)).aestronglyMeasurable
      (ae_of_all _ fun p => ?_)
    rw [Real.norm_eq_abs]
    exact hΦB ω hω _ _
  have hswap := integral_integral_swap hint
  rw [hswap] at hdyn
  exact hdyn.2.symm

end EinsteinFull
