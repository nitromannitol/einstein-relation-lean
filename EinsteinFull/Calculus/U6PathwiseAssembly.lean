import EinsteinFull.Calculus.SunaS2Pathwise
import EinsteinFull.Calculus.C21OccupationUniformIntegrability
import EinsteinFull.Calculus.U5RegularPhysicalCompensator

/-! The pathwise assembly from occupation control of each supplied physical law.
The occupation hypothesis is an intermediate contract, not a source assumption. -/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped ENNReal NNReal Topology

namespace EinsteinFull

/-- Occupation absolute continuity for every supplied physical solution implies
uniqueness of physical solution families in almost every environment. -/
theorem u6_physical_family_unique_of_occupation
    (hocc : ∀ {d : ℕ}, 2 ≤ d → ∀ {Λ : ℝ}, 0 < Λ →
      ∀ {ω : FieldPair d}, IsRegular Λ ω → ∀ (i : Fin d) (lam : ℝ)
        {x : Vec d} {P : Measure (Path d)},
        SolvesMartingaleProblem (physicalGenerator i ω lam) x P →
        Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)))
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (lam : ℝ) (PX PX' : QuenchedPathLaws d)
    (hX : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω)))
    (hX' : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX' (0, ω))) :
    ∀ᵐ ω ∂Q.measure, PX (0, ω) = PX' (0, ω) := by
  have hΛ : 0 < Λ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  filter_upwards [Q.regular, hX, hX'] with ω hω hXω hX'ω
  obtain ⟨P, _, huniq⟩ :=
    (u5_physical_well_posed_iff_occupation_ac hd hΛ hω i lam 0).2
      (fun _ hP => hocc hd hΛ hω i lam hP)
  exact (huniq _ hXω).trans (huniq _ hX'ω).symm

/-- The exact pathwise node follows once occupation absolute continuity is
proved for each supplied literal physical solution. -/
theorem u6_pathwise_of_physical_occupation
    (hocc : ∀ {d : ℕ}, 2 ≤ d → ∀ {Λ : ℝ}, 0 < Λ →
      ∀ {ω : FieldPair d}, IsRegular Λ ω → ∀ (i : Fin d) (lam : ℝ)
        {x : Vec d} {P : Measure (Path d)},
        SolvesMartingaleProblem (physicalGenerator i ω lam) x P →
        Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) :
    Blueprint.node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt :=
  s2_pathwise_of_physical_family_uniqueness (u6_physical_family_unique_of_occupation hocc)

/-- Uniform local control of the smoothed occupation density gives the
same-law small-set test bound. -/
theorem u6_test_small_set_of_smoothed_local_Lq {d : ℕ}
    {P : Measure (Path d)} [IsProbabilityMeasure P]
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (T : ℝ≥0)
    (K : Set (Vec d)) (q C : ℝ)
    (hq : 1 < q)
    (hb : ∀ r : ℝ, 0 < r →
      eLpNorm (fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y)
        ∂Measure.map (fun a : Path d × ℝ => a.1 a.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))))
        (ENNReal.ofReal q) (volume.restrict K) ≤ ENNReal.ofReal C) :
    ∀ s : Set (Vec d), s ⊆ K → MeasurableSet s →
    ∀ φ : Vec d → ℝ, Continuous φ → HasCompactSupport φ →
      (∀ y, ‖φ y‖ ≤ 1) → (∀ y, y ∉ s → φ y = 0) →
    ‖∫ y, φ y ∂Measure.map (fun a : Path d × ℝ => a.1 a.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))‖ₑ ≤
      ENNReal.ofReal C * (volume s) ^ (1 - 1 / (ENNReal.ofReal q).toReal) := by
  intro s hsK hs φ hφ hφc hφbound hφs
  have hq' : (1 : ℝ≥0∞) ≤ ENNReal.ofReal q := by
    simpa using ENNReal.ofReal_le_ofReal hq.le
  apply c21_weak_limit_test_enorm_le (f := fun r y =>
    ∫ z, c16NormalizedPolynomialKernel r m (z-y)
      ∂Measure.map (fun a : Path d × ℝ => a.1 a.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))) volume _ hs hφbound hφs
  · intro r hr
    exact (c16_normalized_polynomial_smoothing_contDiff_one _ hr m).continuous
  · intro r hr
    exact c21_eLpNorm_restrict_one_le volume hsK hq'
      (c16_normalized_polynomial_smoothing_contDiff_one _ hr m).continuous (hb r hr)
  · obtain ⟨B, hB⟩ := hφc.exists_bound_of_continuous hφ
    simpa only [mul_comm] using
      (c21_polynomial_smoothing_weak_convergence hdm
        (Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))))
        (hφ.integrable_of_hasCompactSupport hφc) hφ hB)

/-- Conditional bridge from same-law small-set control to null occupation. -/
theorem u6_finite_null_of_small_set {d : ℕ} {P : Measure (Path d)}
    [IsProbabilityMeasure P]
    (hsmall : ∀ (T : ℝ≥0) (K : Set (Vec d)), IsCompact K →
      ∃ q : ℝ, 1 < q ∧ ∃ C : ℝ, 0 < C ∧ ∀ s : Set (Vec d),
      s ⊆ K → MeasurableSet s → ∀ φ : Vec d → ℝ, Continuous φ →
      HasCompactSupport φ → (∀ y, ‖φ y‖ ≤ 1) → (∀ y, y ∉ s → φ y = 0) →
      ‖∫ y, φ y ∂Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))‖ₑ ≤
        ENNReal.ofReal C * (volume s) ^ (1 - 1 / (ENNReal.ofReal q).toReal))
    {N : Set (Vec d)} (hN : MeasurableSet N)
    (hnull : (volume : Measure (Vec d)) N = 0) (T : ℝ≥0) :
    (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
      {z : Path d × ℝ | z.1 z.2.toNNReal ∈ N} = 0 := by
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
  obtain ⟨q, hq, C, hC, htest⟩ := hsmall T K hK
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


/-- The same explicit small-set estimate yields infinite-time occupation AC. -/
theorem u6_occupation_ac_of_small_set {d : ℕ} {P : Measure (Path d)}
    [IsProbabilityMeasure P]
    (hsmall : ∀ (T : ℝ≥0) (K : Set (Vec d)), IsCompact K →
      ∃ q : ℝ, 1 < q ∧ ∃ C : ℝ, 0 < C ∧ ∀ s : Set (Vec d),
      s ⊆ K → MeasurableSet s → ∀ φ : Vec d → ℝ, Continuous φ →
      HasCompactSupport φ → (∀ y, ‖φ y‖ ≤ 1) → (∀ y, y ∉ s → φ y = 0) →
      ‖∫ y, φ y ∂Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))‖ₑ ≤
        ENNReal.ofReal C * (volume s) ^ (1 - 1 / (ENNReal.ofReal q).toReal)) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  apply c21_averaged_occupation_ac_of_finite_null P
  intro N hN hnull n
  simpa using u6_finite_null_of_small_set hsmall hN hnull (n : ℝ≥0)


#print axioms u6_physical_family_unique_of_occupation
#print axioms u6_pathwise_of_physical_occupation

/-- A same-law nonlinear energy bound controls cutoff entropy in W¹,¹. -/
theorem u6_occupation_cutoff_entropy_W11_of_energy {d : ℕ} (hd : 2 ≤ d) {P : Measure (Path d)} [IsProbabilityMeasure P]
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (T : ℝ≥0)
    (E : ℝ)
    (henergy : ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
      let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
      let e : Vec d → ℝ := fun y => euclideanSq (fun j : Fin d =>
        fderiv ℝ u y (unitVector j)) / (1 + u y) ^ (1 + (2 * (d : ℝ))⁻¹)
      Integrable e (volume : Measure (Vec d)) ∧ (∫ y, e y) ≤ E * (1 + (T : ℝ)))
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
      let u := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
      let v := fun y => χ y * ((1 + u y) ^ (1 - (2 * (d : ℝ))⁻¹) - 1)
      Integrable v (volume : Measure (Vec d)) ∧
      (∀ j : Fin d, Integrable (fun y => fderiv ℝ v y (unitVector j)) volume) ∧
      (∫ y, |v y|) + (∑ j : Fin d, ∫ y, |fderiv ℝ v y (unitVector j)|) ≤ C := by
  let α : ℝ := (2 * (d : ℝ))⁻¹
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hα : 0 < α := by dsimp only [α]; positivity
  have hα1 : α < 1 := by
    dsimp only [α]
    rw [inv_lt_one₀ (by positivity : 0 < 2 * (d : ℝ))]
    linarith
  obtain ⟨B, hB, hχB⟩ := c16_compact_c1_cutoff_uniform_bound hχ hχc
  let D : ℝ := B * ((1 - α) * (E * (1 + (T : ℝ)) +
    ((volume (tsupport χ)).toReal + (T : ℝ))) + 2 * (T : ℝ))
  let C : ℝ := 1 + |B * (T : ℝ)| + (d : ℝ) * |D|
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro r hr
  let μ := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
  let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
  let v : Vec d → ℝ := fun y => χ y * ((1 + u y) ^ (1 - α) - 1)
  obtain ⟨hu, hui, _, hmass⟩ := c16_probability_occupation_normalized_smoothing P T hr m hdm
  obtain ⟨hκ0, _, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  have hu0 (y : Vec d) : 0 ≤ u y := integral_nonneg fun z => (hκ0 (z - y)).le
  have he := henergy r hr
  have hprod := c16_cutoff_sublinear_entropy_c1 hu hu0 hχ hχc hα.le hα1
  refine ⟨hprod.2.2.1, hprod.2.2.2.1, ?_⟩
  have hv := c16_cutoff_sublinear_entropy_integral_bound hu hu0 hui hχ hχc
    hα.le hα1 hB (fun y => (hχB y).1)
  rw [hmass] at hv
  have hv' : (∫ y, |v y|) ≤ |B * (T : ℝ)| := hv.trans (le_abs_self _)
  have hdv (j : Fin d) : (∫ y, |fderiv ℝ v y (unitVector j)|) ≤ |D| := by
    have h := c16_cutoff_sublinear_entropy_derivative_integral_bound
      hu hu0 hui hχ hχc hα.le hα1 he.1 hB hχB j
    rw [hmass] at h
    have he'' : B * ((1 - α) *
        ((∫ y, euclideanSq (gradient u y) / (1 + u y) ^ (1 + α)) +
          ((volume (tsupport χ)).toReal + (T : ℝ))) + 2 * (T : ℝ)) ≤ D := by
      dsimp only [D]
      apply mul_le_mul_of_nonneg_left _ hB
      exact add_le_add (mul_le_mul_of_nonneg_left (add_le_add he.2 le_rfl)
        (by linarith : 0 ≤ 1 - α)) le_rfl
    have hz : 0 ≤ ∫ y, |fderiv ℝ v y (unitVector j)| := integral_nonneg fun _ => abs_nonneg _
    nlinarith [le_abs_self D]
  have hsum : (∑ j : Fin d, ∫ y, |fderiv ℝ v y (unitVector j)|) ≤ (d : ℝ) * |D| := by
    calc
      _ ≤ ∑ _j : Fin d, |D| := Finset.sum_le_sum fun j _ => hdv j
      _ = (d : ℝ) * |D| := by simp
  dsimp only [C]
  linarith


/-- The cutoff entropy obeys a uniform Sobolev estimate under the energy bound. -/
theorem u6_occupation_cutoff_entropy_sobolev_of_energy {d : ℕ} (hd : 2 ≤ d) {P : Measure (Path d)} [IsProbabilityMeasure P]
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (T : ℝ≥0)
    (E : ℝ)
    (henergy : ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
      let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
      let e : Vec d → ℝ := fun y => euclideanSq (fun j : Fin d =>
        fderiv ℝ u y (unitVector j)) / (1 + u y) ^ (1 + (2 * (d : ℝ))⁻¹)
      Integrable e (volume : Measure (Vec d)) ∧ (∫ y, e y) ≤ E * (1 + (T : ℝ)))
    (χ : Vec d → ℝ) (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    ∃ C : ℝ≥0∞, C ≠ ∞ ∧ ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
      let u := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
      let v := fun y => χ y * ((1 + u y) ^ (1 - (2 * (d : ℝ))⁻¹) - 1)
      eLpNorm v ((d : ℝ≥0∞) / ((d : ℝ≥0∞) - 1)) volume ≤ C := by
  obtain ⟨A, hA, hbound⟩ :=
    u6_occupation_cutoff_entropy_W11_of_energy hd m hdm T E henergy χ hχ hχc
  let C₀ : ℝ≥0∞ := ENNReal.ofReal (((d : ℝ) *
    (volume (PDE.euclideanBall (0 : Vec d) 1)).toReal ^ ((1 : ℝ) / d))⁻¹)
  refine ⟨C₀ * ENNReal.ofReal A, ENNReal.mul_ne_top (by simp [C₀]) (by simp), ?_⟩
  intro r hr
  let μ := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
  let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
  let α : ℝ := (2 * (d : ℝ))⁻¹
  let v : Vec d → ℝ := fun y => χ y * ((1 + u y) ^ (1 - α) - 1)
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hα : 0 ≤ α := by dsimp [α]; positivity
  have hα1 : α < 1 := by
    dsimp [α]
    rw [inv_lt_one₀ (by positivity : 0 < 2 * (d : ℝ))]
    linarith
  obtain ⟨hu, _, _, _⟩ := c16_probability_occupation_normalized_smoothing P T hr m hdm
  obtain ⟨hκ0, _, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  have hu0 (y : Vec d) : 0 ≤ u y := integral_nonneg fun z => (hκ0 (z - y)).le
  have hv := c16_cutoff_sublinear_entropy_c1 hu hu0 hχ hχc hα hα1
  have hW := hbound r hr
  have hmass : 0 ≤ ∫ y, |v y| := integral_nonneg fun _ => abs_nonneg _
  have hsum : (∑ j : Fin d, ∫ y, |fderiv ℝ v y (PDE.basisVec j)|) ≤ A := by
    have h := hW.2.2
    simp only [PDE.basisVec, unitVector] at h ⊢
    linarith
  refine (c16_compact_c1_sobolev_bound hd hv.1 hv.2.1).trans ?_
  simpa only [mul_comm] using mul_le_mul_left (ENNReal.ofReal_le_ofReal hsum) C₀


/-- The energy bound implies uniform local Lq control of smoothed occupation. -/
theorem u6_occupation_smoothed_local_Lq_of_energy {d : ℕ} (hd : 2 ≤ d) {P : Measure (Path d)} [IsProbabilityMeasure P]
    (m : ℕ) (hdm : (d : ℝ) < 2 * (m : ℝ)) (T : ℝ≥0)
    (E : ℝ)
    (henergy : ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
      let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
      let e : Vec d → ℝ := fun y => euclideanSq (fun j : Fin d =>
        fderiv ℝ u y (unitVector j)) / (1 + u y) ^ (1 + (2 * (d : ℝ))⁻¹)
      Integrable e (volume : Measure (Vec d)) ∧ (∫ y, e y) ≤ E * (1 + (T : ℝ)))
    (K : Set (Vec d)) (hK : IsCompact K) :
    ∃ q : ℝ, 1 < q ∧ ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r →
      eLpNorm (fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y)
        ∂Measure.map (fun a : Path d × ℝ => a.1 a.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ)))))
        (ENNReal.ofReal q) (volume.restrict K) ≤ ENNReal.ofReal C := by
  let β : ℝ := 1 - (2 * (d : ℝ))⁻¹
  let pR : ℝ := (d : ℝ) / ((d : ℝ) - 1)
  let q : ℝ := β * pR
  let p : ℝ≥0∞ := ENNReal.ofReal pR
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hα0 : 0 ≤ (2 * (d : ℝ))⁻¹ := by positivity
  have hα1 : (2 * (d : ℝ))⁻¹ < 1 := by
    rw [inv_lt_one₀ (by positivity : 0 < 2 * (d : ℝ))]
    linarith
  have hβ : 0 < β := by dsimp [β]; linarith
  have hpR : 1 ≤ pR := by
    dsimp [pR]; rw [le_div_iff₀ (by linarith : 0 < (d : ℝ) - 1)]; linarith
  have hq : 1 < q := by
    simpa [q, β, pR, mul_div_assoc] using c16_occupation_sobolev_exponent_gt_one hd
  have hp : 1 ≤ p := by
    simpa [p] using ENNReal.ofReal_le_ofReal hpR
  have hp0 : p ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one hp)
  have hpt : p ≠ ∞ := by simp [p]
  have hpq : ENNReal.ofReal q * ENNReal.ofReal β⁻¹ = p := by
    rw [← ENNReal.ofReal_mul (by positivity : 0 ≤ q)]
    congr 1
    dsimp [q]
    field_simp
  obtain ⟨χ, hχ, hχc, hχK⟩ := c16_compact_set_smooth_cutoff hK
  obtain ⟨A, hA, hA_bound⟩ :=
    u6_occupation_cutoff_entropy_sobolev_of_energy hd m hdm T E henergy χ hχ hχc
  let N : ℝ≥0∞ := eLpNorm (fun _ : Vec d => (1 : ℝ)) p (volume.restrict K)
  have hN : N ≠ ∞ := by
    apply ne_of_lt
    apply (eLpNorm_const_lt_top_iff hp0 hpt).2
    right
    simpa only [Measure.restrict_apply_univ] using (hK.measure_lt_top : volume K < ∞)
  let D : ℝ≥0∞ := (N + A) ^ β⁻¹
  have hD : D ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.mpr hβ.le)
    (ENNReal.add_ne_top.mpr ⟨hN, hA⟩)
  refine ⟨q, hq, D.toReal + 1, by positivity, ?_⟩
  intro r hr
  let μ := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
    (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
  let u : Vec d → ℝ := fun y => ∫ z, c16NormalizedPolynomialKernel r m (z-y) ∂μ
  let v : Vec d → ℝ := fun y => χ y * ((1 + u y) ^ β - 1)
  obtain ⟨hu, _, _, _⟩ := c16_probability_occupation_normalized_smoothing P T hr m hdm
  obtain ⟨hκ0, _, _, _⟩ := c16_normalized_polynomial_kernel_properties hr m hdm
  have hu0 (y : Vec d) : 0 ≤ u y := integral_nonneg fun z => (hκ0 (z - y)).le
  have hv := c16_cutoff_sublinear_entropy_c1 hu hu0 hχ hχc hα0 hα1
  have hpoint (y : Vec d) (hy : y ∈ K) : v y = (1 + u y) ^ β - 1 := by
    simp [v, hχK y hy]
  have hp_eq : p = (d : ℝ≥0∞) / ((d : ℝ≥0∞) - 1) := by
    simpa [p, pR] using (PDE.SobolevSharp.exponent_eq hd).symm
  have hbound : eLpNorm v p volume ≤ A := by
    rw [hp_eq]
    exact hA_bound r hr
  have htransfer := c16_local_density_norm_le hK hu.continuous hv.1.continuous hu0 hβ hpoint hp hpq
  have hfinal : eLpNorm u (ENNReal.ofReal q) (volume.restrict K) ≤ D := by
    refine htransfer.trans ?_
    exact ENNReal.rpow_le_rpow (add_le_add le_rfl hbound) (inv_nonneg.mpr hβ.le)
  calc
    _ ≤ D := hfinal
    _ = ENNReal.ofReal D.toReal := (ENNReal.ofReal_toReal hD).symm
    _ ≤ ENNReal.ofReal (D.toReal + 1) := ENNReal.ofReal_le_ofReal (by linarith)


/-- A uniform nonlinear-energy estimate gives the requested local test bound
for the same finite occupation measure. -/
theorem u6_local_krylov_of_energy {d : ℕ} (hd : 2 ≤ d)
    {P : Measure (Path d)} [IsProbabilityMeasure P]
    (T : ℝ≥0) (K : Set (Vec d)) (hK : IsCompact K)
    (E : ℝ)
    (henergy : ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
      let u : Vec d → ℝ := fun y =>
        ∫ z, c16NormalizedPolynomialKernel r (d + 1) (z-y) ∂μ
      let e : Vec d → ℝ := fun y => euclideanSq (fun j : Fin d =>
        fderiv ℝ u y (unitVector j)) / (1 + u y) ^ (1 + (2 * (d : ℝ))⁻¹)
      Integrable e (volume : Measure (Vec d)) ∧ (∫ y, e y) ≤ E * (1 + (T : ℝ))) :
    let μT := Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioc (0 : ℝ) (T : ℝ))))
    ∃ q C : ℝ, 1 < q ∧ 0 < C ∧
      ∀ s : Set (Vec d), s ⊆ K → MeasurableSet s →
      ∀ φ : Vec d → ℝ, Continuous φ → HasCompactSupport φ →
      (∀ y, ‖φ y‖ ≤ 1) → (∀ y, y ∉ s → φ y = 0) →
      ‖∫ y, φ y ∂μT‖ₑ ≤ ENNReal.ofReal C *
        (volume s) ^ (1 - 1 / (ENNReal.ofReal q).toReal) := by
  have hdm : (d : ℝ) < 2 * ((d + 1 : ℕ) : ℝ) := by
    push_cast
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨q, hq, C, hC, hb⟩ :=
    u6_occupation_smoothed_local_Lq_of_energy hd (d + 1) hdm T E henergy K hK
  exact ⟨q, C, hq, hC,
    u6_test_small_set_of_smoothed_local_Lq (d + 1) hdm T K q C hq hb⟩


/-- Finite-horizon nonlinear-energy estimates for the same law imply
positive-time averaged occupation absolute continuity. -/
theorem u6_occupation_ac_of_energy {d : ℕ} (hd : 2 ≤ d)
    {P : Measure (Path d)} [IsProbabilityMeasure P]
    (henergy : ∀ T : ℝ≥0, ∃ E : ℝ, 0 < E ∧ ∀ r : ℝ, 0 < r →
      let μ := Measure.map (fun q : Path d × ℝ => q.1 q.2.toNNReal)
        (P.prod (volume.restrict (Set.Ioc 0 (T : ℝ))))
      let u : Vec d → ℝ := fun y =>
        ∫ z, c16NormalizedPolynomialKernel r (d + 1) (z-y) ∂μ
      let e : Vec d → ℝ := fun y => euclideanSq (fun j : Fin d =>
        fderiv ℝ u y (unitVector j)) / (1 + u y) ^ (1 + (2 * (d : ℝ))⁻¹)
      Integrable e (volume : Measure (Vec d)) ∧ (∫ y, e y) ≤ E * (1 + (T : ℝ))) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  apply u6_occupation_ac_of_small_set
  intro T K hK
  obtain ⟨E, hE, hbound⟩ := henergy T
  obtain ⟨q, C, hq, hC, htest⟩ := u6_local_krylov_of_energy hd T K hK E hbound
  exact ⟨q, hq, C, hC, htest⟩


end EinsteinFull
