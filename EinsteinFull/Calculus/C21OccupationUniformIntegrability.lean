import EinsteinFull.Calculus.C21TextbookOccupationAC
import EinsteinFull.Calculus.C16ReducedMPExistence

open MeasureTheory Filter
open scoped ENNReal NNReal Topology

namespace EinsteinFull
open EinsteinRelation

/-- A local higher-exponent bound controls the integral norm on any smaller
measurable set through its measure. -/
theorem c21_eLpNorm_restrict_one_le {d : ℕ} (μ : Measure (Vec d))
    {K s : Set (Vec d)} (hsK : s ⊆ K)
    {q C : ℝ≥0∞} (hq : 1 ≤ q) {f : Vec d → ℝ} (hf : Continuous f)
    (hbound : eLpNorm f q (μ.restrict K) ≤ C) :
    eLpNorm f 1 (μ.restrict s) ≤ C * (μ s) ^ (1 - 1 / q.toReal) := by
  have hm : AEStronglyMeasurable f (μ.restrict s) := hf.measurable.aestronglyMeasurable
  have hqbound : eLpNorm f q (μ.restrict s) ≤ C :=
    (eLpNorm_mono_measure f (Measure.restrict_mono_set μ hsK)).trans hbound
  have h := eLpNorm_le_eLpNorm_mul_rpow_measure_univ hq hm
  calc
    eLpNorm f 1 (μ.restrict s) ≤
        eLpNorm f q (μ.restrict s) * (μ s) ^ (1 - 1 / q.toReal) := by
      simpa [Measure.restrict_apply_univ] using h
    _ ≤ C * (μ s) ^ (1 - 1 / q.toReal) := by gcongr

/-- Local small-set control for the actual smoothed occupation density. -/
theorem c21_textbook_occupation_smoothed_small_set {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)) x P)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (T : ℝ≥0)
    (K : Set (Vec d)) (hK : IsCompact K) :
    ∃ q : ℝ, 1 < q ∧ ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      ∀ s : Set (Vec d), s ⊆ K → MeasurableSet s →
      eLpNorm (fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y)
        ∂Measure.map (fun a : Path d × ℝ => a.1 a.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))))
        1 (volume.restrict s) ≤ ENNReal.ofReal C *
          (volume s) ^ (1 - 1 / (ENNReal.ofReal q).toReal) := by
  obtain ⟨q, hq, C, hC, hb⟩ :=
    c16_textbook_occupation_smoothed_local_Lq hd hΛ hω i lam hP m hdm T K hK
  refine ⟨q, hq, C, hC, ?_⟩
  intro r hr s hsK hs
  let _ : IsProbabilityMeasure P := hP.1
  have hq' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hq.le
  exact c21_eLpNorm_restrict_one_le volume hsK hq'
    (c16_normalized_polynomial_smoothing_contDiff_one _ hr m).continuous (hb r hr)

/-- A bounded test vanishing off a measurable set is controlled by the
restricted integral norm of the density. -/
theorem c21_test_integral_enorm_le_restrict {d : ℕ} (μ : Measure (Vec d))
    {s : Set (Vec d)} (hs : MeasurableSet s) {φ f : Vec d → ℝ}
    (hf : Continuous f) (hφ : ∀ y, ‖φ y‖ ≤ 1)
    (hφs : ∀ y, y ∉ s → φ y = 0) :
    ‖∫ y, φ y * f y ∂μ‖ₑ ≤ eLpNorm f 1 (μ.restrict s) := by
  rw [eLpNorm_one_eq_lintegral_enorm hf.measurable.aestronglyMeasurable,
    ← lintegral_indicator hs]
  refine (enorm_integral_le_lintegral_enorm _).trans ?_
  apply lintegral_mono
  intro y
  by_cases hy : y ∈ s
  · rw [Set.indicator_of_mem hy]
    change ‖φ y * f y‖ₑ ≤ ‖f y‖ₑ
    rw [enorm_mul]
    have h : ‖φ y‖ₑ ≤ 1 := by
      simpa only [← ofReal_norm, ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal (hφ y)
    calc
      ‖φ y‖ₑ * ‖f y‖ₑ ≤ 1 * ‖f y‖ₑ := by gcongr
      _ = ‖f y‖ₑ := one_mul _
  · simp [Set.indicator_of_notMem hy, hφs y hy]

/-- A restricted integral-norm bound passes through a weak test limit. -/
theorem c21_weak_limit_test_enorm_le {d : ℕ} (μ ν : Measure (Vec d))
    {s : Set (Vec d)} (hs : MeasurableSet s) {φ : Vec d → ℝ}
    (hφ : ∀ y, ‖φ y‖ ≤ 1) (hφs : ∀ y, y ∉ s → φ y = 0)
    {f : ℝ → Vec d → ℝ} (hf : ∀ r, 0 < r → Continuous (f r))
    {B : ℝ≥0∞} (hb : ∀ r, 0 < r → eLpNorm (f r) 1 (μ.restrict s) ≤ B)
    (hlim : Tendsto (fun r : ℝ => ∫ y, φ y * f r y ∂μ)
      (𝓝[Set.Ioi (0 : ℝ)] 0) (𝓝 (∫ y, φ y ∂ν))) :
    ‖∫ y, φ y ∂ν‖ₑ ≤ B := by
  apply le_of_tendsto ((continuous_enorm.tendsto _).comp hlim)
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (c21_test_integral_enorm_le_restrict μ hs (hf r hr) hφ hφs).trans (hb r hr)

/-- The occupation measure inherits the small-set bound for compactly
supported tests from the smoothed densities. -/
theorem c21_textbook_occupation_test_small_set {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)) x P)
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (T : ℝ≥0)
    (K : Set (Vec d)) (hK : IsCompact K) :
    ∃ q : ℝ, 1 < q ∧ ∃ C : ℝ, 0 < C ∧
      ∀ s : Set (Vec d), s ⊆ K → MeasurableSet s →
      ∀ φ : Vec d → ℝ, Continuous φ → HasCompactSupport φ →
        (∀ y, ‖φ y‖ ≤ 1) → (∀ y, y ∉ s → φ y = 0) →
      ‖∫ y, φ y ∂Measure.map (fun a : Path d × ℝ => a.1 a.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))‖ₑ ≤
        ENNReal.ofReal C * (volume s) ^ (1 - 1 / (ENNReal.ofReal q).toReal) := by
  obtain ⟨q, hq, C, hC, hb⟩ :=
    c21_textbook_occupation_smoothed_small_set hd hΛ hω i lam hP m hdm T K hK
  refine ⟨q, hq, C, hC, ?_⟩
  intro s hsK hs φ hφ hφc hφbound hφs
  let _ : IsProbabilityMeasure P := hP.1
  apply c21_weak_limit_test_enorm_le (f := fun r y =>
    ∫ z, c16NormalizedPolynomialKernel r m (z-y)
      ∂Measure.map (fun a : Path d × ℝ => a.1 a.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))) volume _ hs hφbound hφs
  · intro r hr
    exact (c16_normalized_polynomial_smoothing_contDiff_one _ hr m).continuous
  · intro r hr
    exact hb r hr s hsK hs
  · exact c21_textbook_occupation_smoothed_weak_limit i lam hP m hdm T φ hφ hφc

/-- A bound on compactly supported tests over an open set bounds every
compact subset of that open set. -/
theorem c21_measure_compact_le_of_test_bound {d : ℕ} (μ : Measure (Vec d))
    [IsFiniteMeasure μ] {L U : Set (Vec d)} (hL : IsCompact L)
    (hU : IsOpen U) (hLU : L ⊆ U) {B : ℝ≥0∞}
    (hb : ∀ φ : Vec d → ℝ, Continuous φ → HasCompactSupport φ →
      (∀ y, ‖φ y‖ ≤ 1) → (∀ y, y ∉ U → φ y = 0) →
      ‖∫ y, φ y ∂μ‖ₑ ≤ B) : μ L ≤ B := by
  have hdis : Disjoint L Uᶜ := Set.disjoint_left.mpr (by
    intro y hyL hyU
    exact hyU (hLU hyL))
  obtain ⟨φ, hφ1, hφ0, hφc, hφrange⟩ :=
    exists_continuous_one_zero_of_isCompact hL hU.isClosed_compl hdis
  have hφint : Integrable φ μ := φ.continuous.integrable_of_hasCompactSupport hφc
  have hintnonneg : 0 ≤ ∫ y, φ y ∂μ := integral_nonneg (fun y => (hφrange y).1)
  calc
    μ L ≤ ENNReal.ofReal (∫ y, φ y ∂μ) :=
      hφint.measure_le_integral (Filter.Eventually.of_forall (fun y => (hφrange y).1))
        (fun y hy => by simpa using le_of_eq (hφ1 hy).symm)
    _ = ‖∫ y, φ y ∂μ‖ₑ := (Real.enorm_eq_ofReal hintnonneg).symm
    _ ≤ B := hb φ φ.continuous hφc
      (fun y => by simpa [Real.norm_eq_abs, abs_of_nonneg (hφrange y).1] using (hφrange y).2)
      (fun y hy => by simpa using hφ0 hy)

/-- A power bound on arbitrarily small open neighbourhoods annihilates
sets of zero measure. -/
theorem c21_null_of_open_power_bound {d : ℕ} (μ ν : Measure (Vec d))
    [Measure.OuterRegular ν] {L : Set (Vec d)} (hnull : ν L = 0)
    {C : ℝ≥0∞} (hC : C ≠ ∞) {a : ℝ} (ha : 0 < a)
    (hb : ∀ U : Set (Vec d), IsOpen U → L ⊆ U → μ L ≤ C * (ν U) ^ a) :
    μ L = 0 := by
  by_contra hne
  have hpos : 0 < μ L := pos_iff_ne_zero.mpr hne
  have hev : ∀ᶠ x : ℝ≥0∞ in 𝓝 0, C * x ^ a < μ L :=
    (ENNReal.tendsto_const_mul_rpow_nhds_zero_of_pos hC ha).eventually
      (Iio_mem_nhds hpos)
  obtain ⟨δ, hδ, hδbound⟩ := ENNReal.nhds_zero_basis.mem_iff.mp hev
  obtain ⟨U, hLU, hU, hvol⟩ := L.exists_isOpen_lt_of_lt (μ := ν) δ (by simpa [hnull] using hδ)
  exact (not_lt_of_ge (hb U hU hLU)) (hδbound hvol)

/-- A Lebesgue-null spatial set has zero finite-horizon occupation under
the supplied textbook martingale law. -/
theorem c21_textbook_null_occupation_finite {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d} (hω : IsRegular Λ₀ ω)
    (i : Fin d) (lam : ℝ) {x : Vec d} {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)) x P)
    {N : Set (Vec d)} (hN : MeasurableSet N)
    (hnull : (volume : Measure (Vec d)) N = 0) (T : ℝ≥0) :
    (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
      {z : Path d × ℝ | z.1 z.2.toNNReal ∈ N} = 0 := by
  let _ : IsProbabilityMeasure P := hP.1
  let μ : Measure (Vec d) := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
  have heval : Measurable (fun z : Path d × ℝ => z.1 z.2.toNNReal) :=
    (continuous_eval.comp
      (continuous_fst.prodMk (continuous_real_toNNReal.comp continuous_snd))).measurable
  have hmap : μ N = (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
      {z : Path d × ℝ | z.1 z.2.toNNReal ∈ N} := Measure.map_apply heval hN
  rw [← hmap, hN.measure_eq_iSup_isCompact μ]
  simp only [ENNReal.iSup_eq_zero]
  intro L hLN hL
  obtain ⟨b, hb⟩ := hL.isBounded.exists_norm_le
  let K : Set (Vec d) := Metric.closedBall 0 (|b| + 1)
  have hK : IsCompact K := isCompact_closedBall (0 : Vec d) (|b| + 1)
  have hLK : L ⊆ interior K := by
    have hballK : Metric.ball (0 : Vec d) (|b| + 1) ⊆ interior K :=
      (Metric.isOpen_ball.subset_interior_iff).2 Metric.ball_subset_closedBall
    apply Set.Subset.trans _ hballK
    intro y hy
    rw [Metric.mem_ball, dist_zero_right]
    have hyb := hb y hy
    linarith [le_abs_self b]
  let m : ℕ := d + 1
  have hdm : (d : ℝ) < 2 * (m : ℝ) := by
    dsimp [m]
    push_cast
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨q, hq, C, hC, htest⟩ :=
    c21_textbook_occupation_test_small_set hd hΛ hω i lam hP m hdm T K hK
  have ha : 0 < 1 - 1 / (ENNReal.ofReal q).toReal := by
    rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ q)]
    have hdiv : 1 / q < 1 := (div_lt_one₀ (by linarith : 0 < q)).2 hq
    linarith
  apply c21_null_of_open_power_bound μ volume (measure_mono_null hLN hnull)
    ENNReal.ofReal_ne_top ha
  intro U hU hLU
  have hV : IsOpen (U ∩ interior K) := hU.inter isOpen_interior
  have hLV : L ⊆ U ∩ interior K := fun y hy => ⟨hLU hy, hLK hy⟩
  have hVK : U ∩ interior K ⊆ K := Set.inter_subset_right.trans interior_subset
  have hbound : μ L ≤ ENNReal.ofReal C *
      (volume (U ∩ interior K)) ^ (1 - 1 / (ENNReal.ofReal q).toReal) := by
    apply c21_measure_compact_le_of_test_bound μ hL hV hLV
    intro φ hφ hφc hφbound hφs
    exact htest (U ∩ interior K) hVK hV.measurableSet φ hφ hφc hφbound hφs
  exact hbound.trans (by gcongr; exact Set.inter_subset_left)

end EinsteinFull
