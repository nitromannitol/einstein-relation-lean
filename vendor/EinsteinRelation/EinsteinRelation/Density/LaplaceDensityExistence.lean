import EinsteinRelation.Carriers.DensityAnnealedTwins
import EinsteinRelation.Diffusion.GMPFamily
import EinsteinRelation.External.GantertSection7Support
import EinsteinRelation.Probability.ReductionLocality
import EinsteinRelation.Probability.ValidAnnealedLawSupport
import Mathlib.Probability.Distributions.Exponential
import Mathlib.Probability.Distributions.Gamma

/-! # Existence of the reduced Laplace-time density

The reduced environment observed at an independent exponential time has a nonnegative
measurable density with respect to the reduced reference law `Measure.map reduce Q`.
The argument has four steps.

* Stationarity of `Measure.map reduce Q` and Tonelli's theorem show that, for almost every
  environment `ω`, the set of translations `y` with `translate y (reduce ω) ∈ A` is
  Lebesgue-null whenever `A` is null for the reference law.
* At a fixed positive time, the endpoint law of a fixed-environment realization has a
  Lebesgue density, so it gives such a set probability zero.
* The exponential time is almost surely positive, so the observed law of `A` vanishes.
* The Radon-Nikodym derivative of the observed law with respect to the reference law is the
  required density.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal NNReal

namespace EinsteinRelation

/-- The pairs `(ω, y)` for which the translated reduced environment `translate y (reduce ω)`
lies in `A`. -/
def laplaceDensityTranslatedSet {d : ℕ} (A : Set (FieldPair d)) :
    Set (FieldPair d × Vec d) :=
  {p | translate p.2 (reduce p.1) ∈ A}

/-- The reduced observation at a fixed time is measurable along the joint law of the environment
and the path. -/
theorem laplaceDensity_measurable_observation_fixed {d : ℕ} (t : ℝ≥0) :
    Measurable (Carriers.reducedObservationAt (d := d) t) :=
  Probability.measurable_reduce.comp
    (Probability.continuous_translate.measurable.comp
      (((measurable_pathPosition (d := d) t).comp measurable_snd).prodMk measurable_fst))

/-- The reduced observation at the exponential time is jointly measurable in the time and the
environment-path pair. -/
theorem laplaceDensity_measurable_observation {d : ℕ} :
    Measurable (fun z : ℝ × (FieldPair d × Path d) =>
      Carriers.reducedObservationAt z.1.toNNReal z.2) := by
  have hev : Continuous (fun p : ℝ≥0 × Path d => p.2 p.1) :=
    continuous_snd.eval continuous_fst
  have htime : Measurable (fun z : ℝ × (FieldPair d × Path d) =>
      ((z.1.toNNReal, z.2.2) : ℝ≥0 × Path d)) :=
    (continuous_real_toNNReal.measurable.comp measurable_fst).prodMk measurable_snd.snd
  have hpos : Measurable (fun z : ℝ × (FieldPair d × Path d) =>
      pathPosition z.1.toNNReal z.2.2) :=
    hev.measurable.comp htime
  have hdom : Measurable (fun z : ℝ × (FieldPair d × Path d) =>
      (pathPosition z.1.toNNReal z.2.2, z.2.1)) :=
    hpos.prodMk measurable_snd.fst
  exact Probability.measurable_reduce.comp
    (Probability.continuous_translate.measurable.comp hdom)

/-- The translated reduced environment is measurable in the translation parameter. -/
theorem laplaceDensity_measurable_translate_reduce {d : ℕ} (ω : FieldPair d) :
    Measurable (fun y : Vec d => translate y (reduce ω)) := by
  have hc : Measurable (fun _ : Vec d => reduce ω) := measurable_const
  exact Probability.continuous_translate.measurable.comp (measurable_id.prodMk hc)

/-- Stationarity of the reduced reference law makes each translate of a null set null for the
environment law. -/
theorem laplaceDensity_measure_translate_null {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hstat : IsStationary (Measure.map reduce Q))
    {A : Set (FieldPair d)} (hA : MeasurableSet A) (hA0 : Measure.map reduce Q A = 0)
    (y : Vec d) : Q {ω | translate y (reduce ω) ∈ A} = 0 := by
  have hB : MeasurableSet (translate y ⁻¹' A) := Probability.measurable_translate y hA
  calc Q {ω | translate y (reduce ω) ∈ A} = Measure.map reduce Q (translate y ⁻¹' A) :=
        (Measure.map_apply (Probability.measurable_reduce (d := d)) hB).symm
    _ = Measure.map (translate y) (Measure.map reduce Q) A :=
        (Measure.map_apply (Probability.measurable_translate y) hA).symm
    _ = 0 := by rw [hstat y]; exact hA0

/-- For `Q`-almost every environment `ω`, the set of translations `y` with
`translate y (reduce ω) ∈ A` is Lebesgue-null. This follows from Tonelli's theorem applied to
the joint set of pairs `(ω, y)`. -/
theorem laplaceDensity_ae_volume_translate_null {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hstat : IsStationary (Measure.map reduce Q))
    {A : Set (FieldPair d)} (hA : MeasurableSet A) (hA0 : Measure.map reduce Q A = 0) :
    ∀ᵐ ω ∂Q, volume {y : Vec d | translate y (reduce ω) ∈ A} = 0 := by
  have hf : Measurable (fun p : FieldPair d × Vec d => translate p.2 (reduce p.1)) :=
    Probability.continuous_translate.measurable.comp
      (measurable_snd.prodMk (Probability.measurable_reduce.comp measurable_fst))
  have hS : MeasurableSet (laplaceDensityTranslatedSet A) := hA.preimage hf
  have h0 : (Q.prod volume) (laplaceDensityTranslatedSet A) = 0 := by
    rw [Measure.prod_apply_symm hS]
    have hy : ∀ y : Vec d,
        Q ((fun x : FieldPair d => (x, y)) ⁻¹' laplaceDensityTranslatedSet A) = 0 :=
      fun y => laplaceDensity_measure_translate_null Q hstat hA hA0 y
    simp only [hy, lintegral_zero]
  have hae := Measure.ae_ae_of_ae_prod
    (p := fun z : FieldPair d × Vec d => z ∉ laplaceDensityTranslatedSet A)
    (measure_eq_zero_iff_ae_notMem.mp h0)
  filter_upwards [hae] with ω hω
  exact measure_eq_zero_iff_ae_notMem.mpr hω

/-- At a positive time, the endpoint law of a fixed-environment realization has a Lebesgue
density, so it gives probability zero to a Lebesgue-null set. -/
theorem laplaceDensity_endpoint_null {d : ℕ} {hd : 2 ≤ d} {Λ : ℝ} {hΛ : 1 ≤ Λ}
    {ω : FieldPair d} {hω : IsRegular Λ ω} {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : External.GantertSection7Support.GantertFixedEnvironmentRealization
      hd Λ hΛ ω hω lam h0 h1)
    {t : ℝ≥0} (ht : 0 < t) {B : Set (Vec d)} (hB : MeasurableSet B) (hB0 : volume B = 0) :
    (r.pathLaw 0) (pathPosition t ⁻¹' B) = 0 := by
  rw [← Measure.map_apply (measurable_pathPosition (d := d) t) hB, r.pathLaw_endpoint t 0,
    r.transitionKernel_eq_heatKernel t ht 0]
  exact withDensity_absolutelyContinuous volume _ hB0

/-- Evaluation of the annealed joint law of a measurable set as an integral over environments of
the fibre masses. -/
theorem laplaceDensity_annealed_apply {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (Q : Measure α) [IsProbabilityMeasure Q] (K : ProbabilityTheory.Kernel α β)
    (hK : ∀ᵐ a ∂Q, IsProbabilityMeasure (K a)) {T : Set (α × β)} (hT : MeasurableSet T) :
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers Q K hK T =
      ∫⁻ a, (K a) (Prod.mk a ⁻¹' T) ∂Q := by
  have hone : Measurable (1 : α × β → ℝ≥0∞) := measurable_one
  have h := Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_lintegral Q K hK
    (T.indicator 1) (hone.indicator hT)
  rw [lintegral_indicator_one hT] at h
  rw [h]
  refine lintegral_congr fun a => ?_
  have hs : MeasurableSet (Prod.mk a ⁻¹' T) := measurable_prodMk_left hT
  calc ∫⁻ b, T.indicator 1 (a, b) ∂K a = ∫⁻ b, (Prod.mk a ⁻¹' T).indicator 1 b ∂K a := rfl
    _ = (K a) (Prod.mk a ⁻¹' T) := lintegral_indicator_one hs

/-- At a fixed positive time, the annealed probability that the observed environment lies in a
measurable null set of the reduced reference law is zero. -/
theorem laplaceDensity_observed_time_null {d : ℕ} {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    {A : Set (FieldPair d)} (hA : MeasurableSet A) (hA0 : Measure.map reduce Q.measure A = 0)
    {t : ℝ≥0} (ht : 0 < t) :
    Carriers.annealedCoordinateJoint Q.measure P hprob
      {q : FieldPair d × Path d | Carriers.reducedObservationAt t q ∈ A} = 0 := by
  have hT : MeasurableSet {q : FieldPair d × Path d | Carriers.reducedObservationAt t q ∈ A} :=
    hA.preimage (laplaceDensity_measurable_observation_fixed (d := d) t)
  have hvol := laplaceDensity_ae_volume_translate_null Q.measure
    (Probability.isStationary_map_reduce Q.measure Q.stationary) hA hA0
  unfold IsGMPReducedOriginLaw at hGMP
  have hae : ∀ᵐ ω ∂Q.measure, (originLaw P ω)
      (Prod.mk ω ⁻¹' {q : FieldPair d × Path d | Carriers.reducedObservationAt t q ∈ A}) = 0 := by
    filter_upwards [hGMP, hvol] with ω hω hν
    obtain ⟨_, r, hr⟩ := hω
    have hB : MeasurableSet {y : Vec d | translate y (reduce ω) ∈ A} :=
      hA.preimage (laplaceDensity_measurable_translate_reduce ω)
    have hsec : Prod.mk ω ⁻¹' {q : FieldPair d × Path d | Carriers.reducedObservationAt t q ∈ A} =
        pathPosition t ⁻¹' {y : Vec d | translate y (reduce ω) ∈ A} :=
      Set.ext fun γ => Iff.rfl
    rw [hr, hsec]
    exact laplaceDensity_endpoint_null r ht hB hν
  unfold Carriers.annealedCoordinateJoint
  rw [laplaceDensity_annealed_apply Q.measure (originLaw P) hprob hT, lintegral_congr_ae hae,
    lintegral_zero]

/-- The exponential law with positive rate charges only positive times. -/
theorem laplaceDensity_ae_expMeasure_pos (r : ℝ) :
    ∀ᵐ τ ∂(ProbabilityTheory.expMeasure r), 0 < τ := by
  have hm : Measurable (ProbabilityTheory.gammaPDF 1 r) :=
    (ProbabilityTheory.measurable_gammaPDFReal 1 r).ennreal_ofReal
  show ∀ᵐ τ ∂((volume : Measure ℝ).withDensity (ProbabilityTheory.gammaPDF 1 r)), 0 < τ
  rw [ae_withDensity_iff hm]
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 :=
    measure_eq_zero_iff_ae_notMem.mp (Real.volume_singleton (a := (0 : ℝ)))
  filter_upwards [hne] with x hx hpos
  rcases lt_trichotomy x 0 with h | h | h
  · exact absurd (ProbabilityTheory.gammaPDF_of_neg h) hpos
  · exact absurd h hx
  · exact h

/-- The image of a product measure under a measurable map gives measure zero to a measurable set
whenever, for almost every first coordinate, the fibre mass of its preimage vanishes. -/
theorem laplaceDensity_map_prod_apply_eq_zero {α β γ : Type*} [MeasurableSpace α]
    [MeasurableSpace β] [MeasurableSpace γ] (μ : Measure α) (ν : Measure β)
    [SFinite μ] [SFinite ν] {g : α × β → γ} (hg : Measurable g) {A : Set γ}
    (hA : MeasurableSet A) (h : ∀ᵐ a ∂μ, ν (Prod.mk a ⁻¹' (g ⁻¹' A)) = 0) :
    (μ.prod ν).map g A = 0 := by
  rw [Measure.map_apply hg hA, Measure.prod_apply (hg hA), lintegral_congr_ae h, lintegral_zero]

/-- The observed law at the exponential time gives measure zero to every measurable null set of
the reduced reference law. -/
theorem laplaceDensity_observed_null {d : ℕ} {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    (s : {r : ℝ // 0 < r}) {A : Set (FieldPair d)} (hA : MeasurableSet A)
    (hA0 : Measure.map reduce Q.measure A = 0) :
    Carriers.reducedLaplaceObservedLaw Q.measure P hprob s A = 0 := by
  haveI := ProbabilityTheory.isProbabilityMeasure_expMeasure s.2
  haveI : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q.measure P hprob) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q.measure (originLaw P) hprob
  have hzero : ∀ᵐ τ ∂(ProbabilityTheory.expMeasure s.1),
      Carriers.annealedCoordinateJoint Q.measure P hprob
        (Prod.mk τ ⁻¹' ((fun z : ℝ × (FieldPair d × Path d) =>
          Carriers.reducedObservationAt z.1.toNNReal z.2) ⁻¹' A)) = 0 := by
    filter_upwards [laplaceDensity_ae_expMeasure_pos s.1] with τ hτ
    have hset : Prod.mk τ ⁻¹' ((fun z : ℝ × (FieldPair d × Path d) =>
        Carriers.reducedObservationAt z.1.toNNReal z.2) ⁻¹' A) =
        {q : FieldPair d × Path d | Carriers.reducedObservationAt (Real.toNNReal τ) q ∈ A} :=
      Set.ext fun q => Iff.rfl
    rw [hset]
    exact laplaceDensity_observed_time_null hd Q h0 h1 P hprob hGMP hA hA0
      (t := Real.toNNReal τ) (Real.toNNReal_pos.mpr hτ)
  unfold Carriers.reducedLaplaceObservedLaw
  exact laplaceDensity_map_prod_apply_eq_zero (ProbabilityTheory.expMeasure s.1)
    (Carriers.annealedCoordinateJoint Q.measure P hprob)
    (laplaceDensity_measurable_observation (d := d)) hA hzero

/-- The observed law at the exponential time is a probability measure. -/
theorem laplaceDensity_isProbabilityMeasure_observed {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (P : QuenchedPathLaws d)
    (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω)) (s : {r : ℝ // 0 < r}) :
    IsProbabilityMeasure (Carriers.reducedLaplaceObservedLaw Q.measure P hprob s) := by
  haveI := ProbabilityTheory.isProbabilityMeasure_expMeasure s.2
  haveI : IsProbabilityMeasure (Carriers.annealedCoordinateJoint Q.measure P hprob) :=
    Probability.ValidAnnealedLawSupport.annealedJointOnProbabilityFibers_isProbabilityMeasure
      Q.measure (originLaw P) hprob
  unfold Carriers.reducedLaplaceObservedLaw
  infer_instance

/-- The observed law at the exponential time is absolutely continuous with respect to the reduced
reference law `Measure.map reduce Q`. -/
theorem laplaceDensity_observed_absolutelyContinuous {d : ℕ} {Λ₀ r₀ : ℝ} (hd : 2 ≤ d)
    (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ} (h0 : 0 ≤ lam) (h1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam h0 h1 (originLaw P))
    (s : {r : ℝ // 0 < r}) :
    Carriers.reducedLaplaceObservedLaw Q.measure P hprob s ≪ Measure.map reduce Q.measure := by
  unfold Measure.AbsolutelyContinuous
  intro A hA0
  obtain ⟨B, hAB, hBm, hB0⟩ := exists_measurable_superset_of_null hA0
  exact measure_mono_null hAB (laplaceDensity_observed_null hd Q h0 h1 P hprob hGMP s hBm hB0)

/-- A finite measure that is absolutely continuous with respect to a finite measure has a
nonnegative measurable real density with respect to it. -/
theorem laplaceDensity_exists_density {α : Type*} [MeasurableSpace α] (ν μ : Measure α)
    [IsFiniteMeasure ν] [IsFiniteMeasure μ] (h : ν ≪ μ) :
    ∃ rho : α → ℝ, Measurable rho ∧ (∀ w, 0 ≤ rho w) ∧
      ν = μ.withDensity (fun w => ENNReal.ofReal (rho w)) := by
  refine ⟨fun w => (ν.rnDeriv μ w).toReal, (Measure.measurable_rnDeriv ν μ).ennreal_toReal,
    fun w => ENNReal.toReal_nonneg, ?_⟩
  calc ν = μ.withDensity (ν.rnDeriv μ) := (Measure.withDensity_rnDeriv_eq ν μ h).symm
    _ = μ.withDensity (fun w => ENNReal.ofReal ((ν.rnDeriv μ w).toReal)) := by
      refine withDensity_congr_ae ?_
      filter_upwards [Measure.rnDeriv_lt_top ν μ] with w hw
      exact (ENNReal.ofReal_toReal hw.ne).symm

/-- Existence of the exponential-time density `rho_s` of the reduced environment law
(`paper/main.tex:431-437`), for a force `lam` whose origin law is the reduced GMP origin law. -/
theorem exists_reducedLaplaceDensity_of_gmp {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam ≤ 1)
    (P : QuenchedPathLaws d) (hprob : ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw P ω))
    (hGMP : IsGMPReducedOriginLaw hd Q.ellipticity_parameter Q lam hl0.le hl1 (originLaw P))
    (s : {r : ℝ // 0 < r}) :
    ∃ rho : FieldPair d → ℝ, Carriers.IsReducedLaplaceDensity Q.measure P hprob s rho := by
  haveI : IsProbabilityMeasure (Measure.map reduce Q.measure) :=
    inferInstance
  haveI := laplaceDensity_isProbabilityMeasure_observed Q P hprob s
  obtain ⟨rho, hm, hnn, heq⟩ := laplaceDensity_exists_density
    (Carriers.reducedLaplaceObservedLaw Q.measure P hprob s) (Measure.map reduce Q.measure)
    (laplaceDensity_observed_absolutelyContinuous hd Q hl0.le hl1 P hprob hGMP s)
  refine ⟨rho, ?_⟩
  unfold Carriers.IsReducedLaplaceDensity
  exact ⟨hm, hnn, heq⟩

end EinsteinRelation
