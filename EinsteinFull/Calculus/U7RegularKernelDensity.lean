import EinsteinFull.Calculus.U2GMPHeatDensity
import EinsteinFull.Calculus.U2GMPGaugeConjugation
import EinsteinFull.Calculus.U4RegularKernelSmoothing
import EinsteinFull.Calculus.C27RealForceRealization
import MarkovProcess.Semigroup.ResolventComparison

open EinsteinRelation MeasureTheory ProbabilityTheory Filter
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal Topology

namespace EinsteinFull

/-- A compact-test estimate against any locally finite absolutely continuous
reference measure yields absolute continuity at every starting point. -/
theorem u7_regular_signed_kernel_ac_of_ae_weighted_compact_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ν : Measure (Vec d))
    [IsFiniteMeasureOnCompacts ν] (hν : ν ≪ (volume : Measure (Vec d)))
    (M : Vec d → ℝ) (hM : Continuous M) (hM0 : ∀ x, 0 ≤ M x)
    (hbound : ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      (∀ y, 0 ≤ f y) → ∀ᵐ x ∂(volume : Measure (Vec d)),
        (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
          M x * ∫ y, f y ∂ν) :
    ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  intro x
  apply Measure.AbsolutelyContinuous.trans ?_ hν
  apply Measure.absolutelyContinuous_of_le_smul (c := ENNReal.ofReal (M x))
  let : IsFiniteMeasureOnCompacts (ENNReal.ofReal (M x) • ν) :=
    IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  apply u2_measure_le_of_compact_continuous_tests
  intro f hf hfc hfn
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
  have hc : Continuous (fun z => ∫ y, f y ∂P t z) := by
    change Continuous (fun z => ∫ y, g y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z)
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω lam Λ hΛ hω t g).continuous
  have hclosed : IsClosed {z : Vec d | (∫ y, f y ∂P t z) ≤ M z * ∫ y, f y ∂ν} :=
    isClosed_le hc (hM.mul continuous_const)
  have hdense := Measure.dense_of_ae (hbound f hf hfc hfn)
  have hall : {z : Vec d | (∫ y, f y ∂P t z) ≤ M z * ∫ y, f y ∂ν} = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  have hx : (∫ y, f y ∂P t x) ≤ M x * ∫ y, f y ∂ν := by
    have : x ∈ {z : Vec d | (∫ y, f y ∂P t z) ≤ M z * ∫ y, f y ∂ν} := by
      rw [hall]
      exact Set.mem_univ x
    exact this
  simpa [integral_smul_measure, ENNReal.toReal_ofReal (hM0 x), smul_eq_mul] using hx

#print axioms u7_regular_signed_kernel_ac_of_ae_weighted_compact_bound

/-- A continuous, start-dependent compact-test bound upgrades an almost
everywhere estimate to absolute continuity at every starting point. -/
theorem u7_regular_signed_kernel_ac_of_ae_compact_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (M : Vec d → ℝ)
    (hM : Continuous M) (hM0 : ∀ x, 0 ≤ M x)
    (hbound : ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      (∀ y, 0 ≤ f y) → ∀ᵐ x ∂(volume : Measure (Vec d)),
        (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
          M x * ∫ y, f y) :
    ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := by
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  intro x
  apply Measure.absolutelyContinuous_of_le_smul (c := ENNReal.ofReal (M x))
  let : IsFiniteMeasureOnCompacts (ENNReal.ofReal (M x) • (volume : Measure (Vec d))) :=
    IsFiniteMeasureOnCompacts.smul _ ENNReal.ofReal_ne_top
  apply u2_measure_le_of_compact_continuous_tests
  intro f hf hfc hfn
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
  have hc : Continuous (fun z => ∫ y, f y ∂P t z) := by
    change Continuous (fun z => ∫ y, g y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t z)
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω lam Λ hΛ hω t g).continuous
  have hclosed : IsClosed {z : Vec d | (∫ y, f y ∂P t z) ≤ M z * ∫ y, f y} :=
    isClosed_le hc (hM.mul continuous_const)
  have hdense := Measure.dense_of_ae (hbound f hf hfc hfn)
  have hall : {z : Vec d | (∫ y, f y ∂P t z) ≤ M z * ∫ y, f y} = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  have hx : (∫ y, f y ∂P t x) ≤ M x * ∫ y, f y := by
    have : x ∈ {z : Vec d | (∫ y, f y ∂P t z) ≤ M z * ∫ y, f y} := by
      rw [hall]
      exact Set.mem_univ x
    exact this
  simpa [integral_smul_measure, ENNReal.toReal_ofReal (hM0 x), smul_eq_mul] using hx

#print axioms u7_regular_signed_kernel_ac_of_ae_compact_bound

/-- An almost-everywhere compact-test estimate for the physical weighted L²
semigroup transfers to absolute continuity of its regular C₀ kernel at every
start. The reference measure may incorporate a spatial gauge. -/
theorem u7_regular_signed_kernel_ac_of_physical_compact_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ν : Measure (Vec d))
    [IsFiniteMeasureOnCompacts ν] (hν : ν ≪ (volume : Measure (Vec d)))
    (M : Vec d → ℝ) (hM : Continuous M) (hM0 : ∀ x, 0 ≤ M x)
    (hbound : ∀ (f : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f),
      (∀ y, 0 ≤ f y) →
      ∀ᵐ x ∂physicalReversibleMeasure ω hd lam,
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
          ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).toLp f) x ≤
            M x * ∫ y, f y ∂ν) :
    ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := by
  apply u7_regular_signed_kernel_ac_of_ae_weighted_compact_bound
    hd ω lam Λ hΛ hω t ν hν M hM hM0
  intro f hf hfc hfn
  let F := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc
  let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
  have he := u2RegularC0KernelSemigroup_integral_ae hd ω lam Λ hΛ hω t g
    (F.toLp f) F.coeFn_toLp
  have hb := hbound f hf hfc hfn
  apply (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp
  filter_upwards [he, hb] with x he hb
  change (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) = _ at he
  rw [he]
  exact hb

#print axioms u7_regular_signed_kernel_ac_of_physical_compact_bound


/-- Every-start absolute continuity of the regular signed kernel yields a
jointly measurable, nonnegative, normalized real density. -/
theorem u7_regular_signed_kernel_normalized_density_of_absolutelyContinuous {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0)
    (hac : ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d))) :
    ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y) ∧
      (∀ x, Integrable (p x) volume ∧ ∫ y, p x y = 1) ∧
      ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (p x y)) := by
  let K := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t
  let : IsMarkovKernel K := ⟨fun x =>
    ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩⟩
  obtain ⟨p, hp, hn, hr⟩ := u2_kernel_measurable_real_density_of_absolutelyContinuous K hac
  exact ⟨p, hp, hn, u2_markov_real_density_integrable_and_integral K p hp hn hr, hr⟩

#print axioms u7_regular_signed_kernel_normalized_density_of_absolutelyContinuous


/-- A compact-test L² estimate at every start implies absolute continuity. -/
theorem u7_regular_signed_kernel_ac_of_local_L2_bound {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0)
    (hbound : ∀ x, ∃ C : ℝ, 0 < C ∧ ∀ f : Vec d → ℝ,
      Continuous f → HasCompactSupport f →
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        C * (eLpNorm f 2 (physicalReversibleMeasure ω hd lam)).toReal) :
    ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := by
  intro x
  let μ := physicalReversibleMeasure ω hd lam
  let ν := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x
  let : IsLocallyFiniteMeasure μ := EinsteinFull.Work.W5.gantert_physicalMeasure_locallyFinite hd ω lam
  let : IsProbabilityMeasure ν := ⟨u2_regular_kernel_conservative hd ω lam Λ hΛ hω t x⟩
  obtain ⟨C, hC, hbound⟩ := hbound x
  apply Measure.AbsolutelyContinuous.mk
  intro A hA hAz
  rw [hA.measure_eq_iSup_isCompact ν]
  apply le_antisymm ?_ bot_le
  apply iSup_le
  intro K
  apply iSup_le
  intro hKA
  apply iSup_le
  intro hK
  have hKv : (volume : Measure (Vec d)) K = 0 := measure_mono_null hKA hAz
  have hμv : μ ≪ (volume : Measure (Vec d)) := by
    apply Measure.ae_le_iff_absolutelyContinuous.mp
    intro P hP
    exact (Blueprint.gmpPhysical_ae_iff_volume hd ω lam P).mpr hP
  have hKμ : μ K = 0 := hμv hKv
  obtain ⟨c, f, hc, hcc, hcb, hf, hfb, hfl⟩ := u2_compact_indicator_approximation K hK
  have hlimμ : Tendsto (fun n => ∫ y, f n y ∂μ) atTop (𝓝 0) := by
    have hcint : Integrable c μ := hc.integrable_of_hasCompactSupport hcc
    have hh := tendsto_integral_of_dominated_convergence c
      (fun n => (hf n).1.aestronglyMeasurable) hcint
      (fun n => Filter.Eventually.of_forall fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hfb n y).1]
        exact (hfb n y).2)
      (Filter.Eventually.of_forall hfl)
    simpa [integral_indicator_const, hK.isClosed.measurableSet, measureReal_def, hKμ] using hh
  have hsq (n : ℕ) : (eLpNorm (f n) 2 μ).toReal ^ 2 ≤ ∫ y, f n y ∂μ := by
    rw [PDE.toReal_eLpNorm_two_sq_eq_integral_sq
      (Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam (f n) (hf n).1 (hf n).2)]
    apply integral_mono_ae
    · apply ((hf n).1.pow 2).integrable_of_hasCompactSupport
      have hsupp : HasCompactSupport ((f n) * (f n)) := (hf n).2.mul_right
      simpa only [pow_two, Pi.mul_apply] using hsupp
    · exact (hf n).1.integrable_of_hasCompactSupport (hf n).2
    · filter_upwards with y
      nlinarith [(hfb n y).1, (hfb n y).2, (hcb y).2]
  have hnorm : Tendsto (fun n => (eLpNorm (f n) 2 μ).toReal) atTop (𝓝 0) := by
    have hs : Tendsto (fun n => (eLpNorm (f n) 2 μ).toReal ^ 2) atTop (𝓝 0) :=
      squeeze_zero (fun n => sq_nonneg _) hsq hlimμ
    have hh := Real.continuous_sqrt.continuousAt.tendsto.comp hs
    simpa only [Function.comp_def, Real.sqrt_sq (ENNReal.toReal_nonneg), Real.sqrt_zero] using hh
  have hlimν := u2_probability_integral_approximation ν f
    (K.indicator (fun _ => (1 : ℝ))) (fun n => (hf n).1)
    (fun n y => ⟨(hfb n y).1, (hfb n y).2.trans (hcb y).2⟩) hfl
  have hle : (∫ y, K.indicator (fun _ => (1 : ℝ)) y ∂ν) ≤ 0 := by
    apply le_of_tendsto_of_tendsto hlimν (by simpa using hnorm.const_mul C)
    exact Filter.Eventually.of_forall fun n => (le_abs_self _).trans (hbound (f n) (hf n).1 (hf n).2)
  rw [integral_indicator_const (μ := ν) (1 : ℝ) hK.isClosed.measurableSet] at hle
  have hreal : (ν K).toReal = 0 := by
    have hh : (ν K).toReal ≤ 0 := by simpa [measureReal_def] using hle
    exact le_antisymm hh ENNReal.toReal_nonneg
  simpa only [bot_eq_zero, le_zero_iff] using
    ((ENNReal.toReal_eq_zero_iff (ν K)).mp hreal).resolve_right (measure_ne_top ν K)

#print axioms u7_regular_signed_kernel_ac_of_local_L2_bound

/-- Exponential conjugation for the physical generator, with the actual
clock factor retained. The identity holds on a spatial full-measure set. -/
theorem u7_physical_generator_exponential_conjugation_ae {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (f : Vec d → ℝ) (hf : ContDiff ℝ 2 f) :
    let i := firstCoordinateIndex hd
    let h : Vec d → ℝ := fun y => Real.exp (lam * y i)
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      physicalGenerator i ω 0 (fun y => h y * f y) x -
        f x * physicalGenerator i ω 0 h x = h x * physicalGenerator i ω lam f x := by
  filter_upwards [c27_reduced_generator_exponential_conjugation_ae
    (by linarith : 0 < Λ) hω (firstCoordinateIndex hd) lam f hf] with x hx
  have h1 := clockDensity_mul_physicalGenerator (firstCoordinateIndex hd) ω 0
    (fun y => Real.exp (lam * y (firstCoordinateIndex hd)) * f y) x
  have h2 := clockDensity_mul_physicalGenerator (firstCoordinateIndex hd) ω 0
    (fun y => Real.exp (lam * y (firstCoordinateIndex hd))) x
  have h3 := clockDensity_mul_physicalGenerator (firstCoordinateIndex hd) ω lam f x
  have hc : 0 < clockDensity ω x := by simp [clockDensity, Real.exp_pos]
  rw [← h1, ← h2, ← h3] at hx
  apply (mul_left_cancel₀ (ne_of_gt hc))
  nlinarith [hx]

#print axioms u7_physical_generator_exponential_conjugation_ae

/-- The physical gauge potential uses the inverse clock density. -/
noncomputable def u7PhysicalGaugePotential {d : ℕ}
    (ω : FieldPair d) (i : Fin d) (lam : ℝ) (x : Vec d) : ℝ :=
  (clockDensity ω x)⁻¹ *
    (lam * forcedDrift (reducedCoefficient ω) i 0 x i +
      (lam ^ 2 / 2) * reducedCoefficient ω x i i)

/-- The actual physical gauge potential is measurable and bounded uniformly in space. -/
theorem u7_physical_gauge_potential_bounded {d : ℕ}
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (i : Fin d) :
    Measurable (u7PhysicalGaugePotential ω i lam) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ x, |u7PhysicalGaugePotential ω i lam x| ≤ C := by
  obtain ⟨hm, M, hM, hb⟩ := c25_reduced_force_potential_bounded
    (by linarith : 0 < Λ) hω i lam
  have hc : Continuous (fun x : Vec d => (clockDensity ω x)⁻¹) := by
    have he : (fun x : Vec d => (clockDensity ω x)⁻¹) =
        (fun x => Real.exp (2 * ω.2 x)) := by
      funext x
      rw [clockDensity, ← Real.exp_neg]
      congr 1
      ring
    rw [he]
    exact Real.continuous_exp.comp (continuous_const.mul ω.2.continuous)
  constructor
  · exact hc.measurable.mul hm
  · refine ⟨Real.exp (2 * Λ) * M + 1, by positivity, ?_⟩
    intro x
    calc
      |u7PhysicalGaugePotential ω i lam x| =
          |(clockDensity ω x)⁻¹| *
            |lam * forcedDrift (reducedCoefficient ω) i 0 x i +
              (lam ^ 2 / 2) * reducedCoefficient ω x i i| := by
                rw [u7PhysicalGaugePotential, abs_mul]
      _ ≤ Real.exp (2 * Λ) * M := mul_le_mul
          (abs_clockDensity_inv_le hω x) (hb x) (abs_nonneg _) (Real.exp_pos _).le
      _ ≤ Real.exp (2 * Λ) * M + 1 := by linarith

/-- The gauge potential is the quotient of the unforced physical generator
on the coordinate exponential. -/
theorem u7_physical_generator_exponential_potential_ae {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) :
    let i := firstCoordinateIndex hd
    let h : Vec d → ℝ := fun y => Real.exp (lam * y i)
    ∀ᵐ x ∂(volume : Measure (Vec d)),
      physicalGenerator i ω 0 h x = h x * u7PhysicalGaugePotential ω i lam x := by
  filter_upwards [c27_reduced_generator_exponential_potential_ae
    (by linarith : 0 < Λ) hω (firstCoordinateIndex hd) lam] with x hx
  rw [physicalGenerator_eq_inv_mul, hx]
  simp only [u7PhysicalGaugePotential]
  ring

#print axioms u7_physical_gauge_potential_bounded
#print axioms u7_physical_generator_exponential_potential_ae

/-- A gauge comparison on compact tests holding almost everywhere extends to
all starting points, since both physical kernel actions are continuous. -/
theorem u7_regular_gauge_compact_comparison_every_start {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (C : ℝ)
    (f : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f)
    (hbound : ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        Real.exp (C * (t : ℝ) - lam * x (firstCoordinateIndex hd)) *
          ∫ y, Real.exp (lam * y (firstCoordinateIndex hd)) * f y
            ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) :
    ∀ x, (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        Real.exp (C * (t : ℝ) - lam * x (firstCoordinateIndex hd)) *
          ∫ y, Real.exp (lam * y (firstCoordinateIndex hd)) * f y
            ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x := by
  let g : Vec d → ℝ := fun y => Real.exp (lam * y (firstCoordinateIndex hd)) * f y
  have hg : Continuous g :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _))).mul hf
  have hgc : HasCompactSupport g := hfc.mul_left
  let F : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
  let G : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨g, hg⟩, hgc.is_zero_at_infty⟩
  have hleft : Continuous (fun x => ∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) := by
    change Continuous (fun x => ∫ y, F y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x)
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω lam Λ hΛ hω t F).continuous
  have hright : Continuous (fun x => ∫ y, g y ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) := by
    change Continuous (fun x => ∫ y, G y ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x)
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω 0 Λ hΛ hω t G).continuous
  have hclosed : IsClosed {x : Vec d |
      (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        Real.exp (C * (t : ℝ) - lam * x (firstCoordinateIndex hd)) *
          ∫ y, g y ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x} :=
    isClosed_le hleft ((Real.continuous_exp.comp
      (continuous_const.sub (continuous_const.mul (continuous_apply _)))).mul hright)
  have hdense := Measure.dense_of_ae hbound
  have hall : {x : Vec d |
      (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        Real.exp (C * (t : ℝ) - lam * x (firstCoordinateIndex hd)) *
          ∫ y, g y ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x} = Set.univ := by
    rw [← hclosed.closure_eq, hdense.closure_eq]
  intro x
  have hx : x ∈ {x : Vec d |
      (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        Real.exp (C * (t : ℝ) - lam * x (firstCoordinateIndex hd)) *
          ∫ y, g y ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x} := by
    rw [hall]
    exact Set.mem_univ x
  exact hx

#print axioms u7_regular_gauge_compact_comparison_every_start

/-- Weighting a locally finite measure by a nonnegative continuous function
preserves finiteness on compact sets. -/
theorem u7_withDensity_continuous_finite_on_compacts {d : ℕ}
    (μ : Measure (Vec d)) [IsFiniteMeasureOnCompacts μ]
    (w : Vec d → ℝ) (hw : Continuous w) :
    IsFiniteMeasureOnCompacts (μ.withDensity (fun x => ENNReal.ofReal (w x))) := by
  constructor
  intro K hK
  rw [withDensity_apply _ hK.isClosed.measurableSet]
  obtain ⟨B, hB⟩ := hK.bddAbove_image hw.continuousOn
  apply setLIntegral_lt_top_of_le_nnreal (hK.measure_ne_top (μ := μ))
  refine ⟨Real.toNNReal B, ?_⟩
  intro x hx
  have hxB : w x ≤ B := hB ⟨x, hx, rfl⟩
  change ENNReal.ofReal (w x) ≤ ENNReal.ofReal B
  exact ENNReal.ofReal_le_ofReal hxB

#print axioms u7_withDensity_continuous_finite_on_compacts

/-- An almost-everywhere gauge comparison on nonnegative compact tests
implies the corresponding measurable-set domination at every start. -/
theorem u7_regular_gauge_domination_of_ae_compact_comparison {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (C : ℝ)
    (hbound : ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      (∀ y, 0 ≤ f y) → ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        Real.exp (C * (t : ℝ) - lam * x (firstCoordinateIndex hd)) *
          ∫ y, Real.exp (lam * y (firstCoordinateIndex hd)) * f y
            ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) :
    ∀ (x : Vec d) (s : Set (Vec d)), MeasurableSet s →
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x s ≤
        ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
          ∫⁻ y in s, ENNReal.ofReal (Real.exp (lam * ((y - x) (firstCoordinateIndex hd))))
            ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x := by
  intro x s hs
  let P := u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω
  let Q := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  let : IsFiniteKernel (Q t) := (Q.isSubMarkovKernel t).isFiniteKernel
  let a := Real.exp (C * (t : ℝ) - lam * x (firstCoordinateIndex hd))
  let w : Vec d → ℝ := fun y => a * Real.exp (lam * y (firstCoordinateIndex hd))
  have hw : Continuous w := continuous_const.mul
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _)))
  have hw0 : ∀ y, 0 ≤ w y := fun y => mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le
  let ν := (Q t x).withDensity (fun y => ENNReal.ofReal (w y))
  let : IsFiniteMeasureOnCompacts ν := u7_withDensity_continuous_finite_on_compacts (Q t x) w hw
  have hle : P t x ≤ ν := by
    apply u2_measure_le_of_compact_continuous_tests
    intro f hf hfc hfn
    have hc := u7_regular_gauge_compact_comparison_every_start hd ω lam Λ hΛ hω t C f hf hfc
      (hbound f hf hfc hfn) x
    change (∫ y, f y ∂P t x) ≤ ∫ y, f y ∂ν
    rw [show ν = (Q t x).withDensity (fun y => ENNReal.ofReal (w y)) from rfl,
      integral_withDensity_eq_integral_toReal_smul hw.measurable.ennreal_ofReal
        (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top) f]
    simp only [ENNReal.toReal_ofReal (hw0 _), smul_eq_mul, w]
    simp_rw [mul_assoc, integral_const_mul]
    exact hc
  have hw_eq (y : Vec d) : w y = Real.exp (C * (t : ℝ)) *
      Real.exp (lam * ((y - x) (firstCoordinateIndex hd))) := by
    dsimp only [w, a, Pi.sub_apply]
    rw [← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  calc
    P t x s ≤ ν s := hle s
    _ = ∫⁻ y in s, ENNReal.ofReal (w y) ∂Q t x := withDensity_apply _ hs
    _ = ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
          ∫⁻ y in s, ENNReal.ofReal (Real.exp (lam * ((y - x) (firstCoordinateIndex hd))))
            ∂Q t x := by
      simp_rw [hw_eq, ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

#print axioms u7_regular_gauge_domination_of_ae_compact_comparison

/-- Almost-everywhere compact-test gauge comparison yields absolute continuity
of the signed kernel at every starting point and positive time. -/
theorem u7_regular_signed_kernel_ac_of_ae_gauge_comparison {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) (C : ℝ)
    (hbound : ∀ f : Vec d → ℝ, Continuous f → HasCompactSupport f →
      (∀ y, 0 ≤ f y) → ∀ᵐ x ∂(volume : Measure (Vec d)),
      (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ≤
        Real.exp (C * (t : ℝ) - lam * x (firstCoordinateIndex hd)) *
          ∫ y, Real.exp (lam * y (firstCoordinateIndex hd)) * f y
            ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) :
    ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := by
  obtain ⟨M, p, hM, hp, hpb, hrep⟩ :=
    u2_regular_unforced_kernel_bounded_density hd ω Λ hΛ hω t ht
  intro x
  have hac : u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := by
    rw [hrep x]
    exact withDensity_absolutelyContinuous _ _
  apply Measure.AbsolutelyContinuous.mk
  intro s hs hs0
  have hzero := hac hs0
  have h := u7_regular_gauge_domination_of_ae_compact_comparison
    hd ω lam Λ hΛ hω t C hbound x s hs
  rw [Measure.restrict_eq_zero.mpr hzero, lintegral_zero_measure, mul_zero] at h
  exact le_antisymm h bot_le

#print axioms u7_regular_signed_kernel_ac_of_ae_gauge_comparison

/-- A comparison of the actual physical L² semigroups on gauged compact
continuous tests implies signed-kernel absolute continuity at every start. -/
theorem u7_regular_signed_kernel_ac_of_physical_gauge_comparison {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) (C : ℝ)
    (hbound : ∀ (f : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f),
      (∀ y, 0 ≤ f y) →
      let g := fun y => Real.exp (lam * y (firstCoordinateIndex hd)) * f y
      let hg : Continuous g :=
        (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _))).mul hf
      let hgc : HasCompactSupport g := hfc.mul_left
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
          ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).toLp f) x ≤
        Real.exp (C * (t : ℝ) - lam * x (firstCoordinateIndex hd)) *
          Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t
            ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 g hg hgc).toLp g) x) :
    ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := by
  apply u7_regular_signed_kernel_ac_of_ae_gauge_comparison hd ω lam Λ hΛ hω t ht C
  intro f hf hfc hfn
  let g : Vec d → ℝ := fun y => Real.exp (lam * y (firstCoordinateIndex hd)) * f y
  have hg : Continuous g :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _))).mul hf
  have hgc : HasCompactSupport g := hfc.mul_left
  let F := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc
  let G := Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 g hg hgc
  let f0 : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
  let g0 : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨g, hg⟩, hgc.is_zero_at_infty⟩
  have hf_eq := u2RegularC0KernelSemigroup_integral_ae hd ω lam Λ hΛ hω t f0
    (F.toLp f) F.coeFn_toLp
  have hg_eq := u2RegularC0KernelSemigroup_integral_ae hd ω 0 Λ hΛ hω t g0
    (G.toLp g) G.coeFn_toLp
  have hf_vol := (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp hf_eq
  have hg_vol := (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 _).mp hg_eq
  filter_upwards [hf_vol, hg_vol, hbound f hf hfc hfn] with x hfx hgx hx
  change (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) = _ at hfx
  change (∫ y, g y ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) = _ at hgx
  rw [hfx, hgx]
  exact hx

#print axioms u7_regular_signed_kernel_ac_of_physical_gauge_comparison

/-- An actual physical L² semigroup comparison on gauged compact tests
implies the corresponding measure domination at every start. -/
theorem u7_regular_gauge_domination_of_physical_gauge_comparison {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (C : ℝ)
    (hbound : ∀ (f : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f),
      (∀ y, 0 ≤ f y) →
      let g := fun y => Real.exp (lam * y (firstCoordinateIndex hd)) * f y
      let hg : Continuous g :=
        (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _))).mul hf
      let hgc : HasCompactSupport g := hfc.mul_left
      ∀ᵐ x ∂(volume : Measure (Vec d)),
        Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
          ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).toLp f) x ≤
        Real.exp (C * (t : ℝ) - lam * x (firstCoordinateIndex hd)) *
          Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t
            ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 g hg hgc).toLp g) x) :
    ∀ (x : Vec d) (s : Set (Vec d)), MeasurableSet s →
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x s ≤
        ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
          ∫⁻ y in s, ENNReal.ofReal (Real.exp (lam * ((y - x) (firstCoordinateIndex hd))))
            ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x := by
  apply u7_regular_gauge_domination_of_ae_compact_comparison hd ω lam Λ hΛ hω t C
  intro f hf hfc hfn
  let g : Vec d → ℝ := fun y => Real.exp (lam * y (firstCoordinateIndex hd)) * f y
  have hg : Continuous g :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _))).mul hf
  have hgc : HasCompactSupport g := hfc.mul_left
  let F := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc
  let G := Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 g hg hgc
  let f0 : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
  let g0 : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨g, hg⟩, hgc.is_zero_at_infty⟩
  have hf_eq := u2RegularC0KernelSemigroup_integral_ae hd ω lam Λ hΛ hω t f0
    (F.toLp f) F.coeFn_toLp
  have hg_eq := u2RegularC0KernelSemigroup_integral_ae hd ω 0 Λ hΛ hω t g0
    (G.toLp g) G.coeFn_toLp
  have hf_vol := (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp hf_eq
  have hg_vol := (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 _).mp hg_eq
  filter_upwards [hf_vol, hg_vol, hbound f hf hfc hfn] with x hfx hgx hx
  change (∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) = _ at hfx
  change (∫ y, g y ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x) = _ at hgx
  rw [hfx, hgx]
  exact hx


#print axioms u7_regular_gauge_domination_of_physical_gauge_comparison

private instance u7LpOrderedModule {α : Type*} [MeasurableSpace α] (μ : Measure α) :
    IsOrderedModule ℝ (Lp ℝ 2 μ) where
  smul_le_smul_of_nonneg_left := by
    intro a ha f g hfg
    rw [← Lp.coeFn_le] at hfg ⊢
    filter_upwards [Lp.coeFn_smul a f, Lp.coeFn_smul a g, hfg] with x hf hg h
    simpa only [hf, hg, Pi.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_left h ha
  smul_le_smul_of_nonneg_right := by
    intro f hf a b hab
    rw [← Lp.coeFn_nonneg] at hf
    rw [← Lp.coeFn_le]
    filter_upwards [Lp.coeFn_smul a f, Lp.coeFn_smul b f, hf] with x ha hb h
    simpa only [ha, hb, Pi.smul_apply, smul_eq_mul] using mul_le_mul_of_nonneg_right hab h

/-- Resolvent order gives the corresponding comparison after smoothing both
orbits. This does not require the two generator domains to coincide. -/
theorem u7_resolvent_smoothed_semigroup_comparison
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S T : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (Lp ℝ 2 μ))
    (r : MarkovProcess.Semigroup.PositiveShift)
    (hS : ∀ (t : ℝ≥0) (f : Lp ℝ 2 μ), 0 ≤ f → 0 ≤ S t f)
    (hT : ∀ (t : ℝ≥0) (f : Lp ℝ 2 μ), 0 ≤ f → 0 ≤ T t f)
    (hR : ∀ f : Lp ℝ 2 μ, 0 ≤ f → T.resolvent r f ≤ S.resolvent r f)
    (t : ℝ≥0) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
    S.resolvent r (T t (T.resolvent r f)) ≤
      S t (S.resolvent r (T.resolvent r f)) := by
  apply sub_nonneg.mp
  rw [S.operator_resolvent_sub_resolvent_operator_eq_integral T r t f,
    intervalIntegral.integral_of_le t.coe_nonneg]
  apply integral_nonneg
  intro y
  apply hS
  apply sub_nonneg.mpr
  exact hR _ (hT _ _ hf)

#print axioms u7_resolvent_smoothed_semigroup_comparison

/-- Positive contraction semigroups inherit order from their resolvents at
every positive shift. -/
theorem u7_semigroup_comparison_of_resolvent_order
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S T : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (Lp ℝ 2 μ))
    (hS : ∀ (t : ℝ≥0) (f : Lp ℝ 2 μ), 0 ≤ f → 0 ≤ S t f)
    (hT : ∀ (t : ℝ≥0) (f : Lp ℝ 2 μ), 0 ≤ f → 0 ≤ T t f)
    (hR : ∀ (r : MarkovProcess.Semigroup.PositiveShift) (f : Lp ℝ 2 μ),
      0 ≤ f → T.resolvent r f ≤ S.resolvent r f)
    (t : ℝ≥0) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) : T t f ≤ S t f := by
  let A := S.toContractiveResolvent
  let B := T.toContractiveResolvent
  have hB : Tendsto (fun r => B.scaledOperator r f) atTop (𝓝 f) :=
    B.tendsto_scaledOperator_apply f
  have hinner : Tendsto (fun r => A.scaledOperator r (B.scaledOperator r f)) atTop (𝓝 f) := by
    exact MarkovProcess.Semigroup.tendsto_apply_of_opNorm_le_one
      A.scaledOperator (ContinuousLinearMap.id ℝ _) _ f
      A.opNorm_scaledOperator_le_one (by simpa using A.tendsto_scaledOperator_apply f) hB
  have hl : Tendsto (fun r => A.scaledOperator r (T t (B.scaledOperator r f)))
      atTop (𝓝 (T t f)) := by
    apply MarkovProcess.Semigroup.tendsto_apply_of_opNorm_le_one
      A.scaledOperator (ContinuousLinearMap.id ℝ _) _ (T t f)
      A.opNorm_scaledOperator_le_one
    · simpa using A.tendsto_scaledOperator_apply (T t f)
    · exact (T t).continuous.tendsto f |>.comp hB
  have hr : Tendsto (fun r => S t (A.scaledOperator r (B.scaledOperator r f)))
      atTop (𝓝 (S t f)) := (S t).continuous.tendsto f |>.comp hinner
  apply le_of_tendsto_of_tendsto hl hr
  filter_upwards with r
  have h := u7_resolvent_smoothed_semigroup_comparison μ S T r hS hT (hR r) t f hf
  have hr0 : 0 ≤ (r : ℝ) := le_of_lt r.property
  have h' := smul_le_smul_of_nonneg_left (smul_le_smul_of_nonneg_left h hr0) hr0
  simpa only [A, B, MarkovProcess.Semigroup.ContractiveResolvent.scaledOperator,
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.toContractiveResolvent_operator,
    ContinuousLinearMap.smul_apply, map_smul, smul_smul] using h'

#print axioms u7_semigroup_comparison_of_resolvent_order

/-- The resolvent of a positive contraction semigroup is positive. -/
theorem u7_positive_semigroup_resolvent_positive
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (Lp ℝ 2 μ))
    (hS : ∀ (t : ℝ≥0) (f : Lp ℝ 2 μ), 0 ≤ f → 0 ≤ S t f)
    (r : MarkovProcess.Semigroup.PositiveShift) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
    0 ≤ S.resolvent r f := by
  change 0 ≤ ∫ t in Set.Ioi (0 : ℝ), S.laplaceIntegrand r f t
  apply integral_nonneg
  intro t
  rw [S.laplaceIntegrand_apply]
  exact smul_nonneg (Real.exp_nonneg _) (hS _ f hf)

/-- Full-domain generator order implies resolvent order. The domain inclusion
is essential: compact-test generator identities alone do not suffice. -/
theorem u7_resolvent_order_of_generator_order
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S T : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (Lp ℝ 2 μ))
    (hS : ∀ (t : ℝ≥0) (f : Lp ℝ 2 μ), 0 ≤ f → 0 ≤ S t f)
    (hT : ∀ (t : ℝ≥0) (f : Lp ℝ 2 μ), 0 ≤ f → 0 ≤ T t f)
    (hdom : T.generatorDomain ≤ S.generatorDomain)
    (hgen : ∀ (v : T.generatorDomain) (_hv : 0 ≤ (v : Lp ℝ 2 μ)),
      T.generator v ≤ S.generator ⟨v, hdom v.property⟩)
    (r : MarkovProcess.Semigroup.PositiveShift) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
    T.resolvent r f ≤ S.resolvent r f := by
  let v : T.generatorDomain := ⟨T.resolvent r f, T.resolvent_mem_generatorDomain r f⟩
  have hv : 0 ≤ (v : Lp ℝ 2 μ) := u7_positive_semigroup_resolvent_positive μ T hT r f hf
  have hi : (r : ℝ) • (v : Lp ℝ 2 μ) - S.generator ⟨v, hdom v.property⟩ ≤ f := by
    have ht := T.generator_resolvent r f
    have hg := hgen v hv
    dsimp only [v] at ht hg ⊢
    calc
      (r : ℝ) • T.resolvent r f -
          S.generator ⟨T.resolvent r f, hdom (T.resolvent_mem_generatorDomain r f)⟩ ≤
          (r : ℝ) • T.resolvent r f -
            T.generator ⟨T.resolvent r f, T.resolvent_mem_generatorDomain r f⟩ :=
        sub_le_sub_left hg _
      _ = f := by rw [ht]; abel
  have hp : 0 ≤ S.resolvent r (f - ((r : ℝ) • (v : Lp ℝ 2 μ) -
      S.generator ⟨v, hdom v.property⟩)) :=
    u7_positive_semigroup_resolvent_positive μ S hS r _ (sub_nonneg.mpr hi)
  rw [map_sub] at hp
  have hres := S.resolvent_smul_sub_generator r ⟨(v : Lp ℝ 2 μ), hdom v.property⟩
  change S.resolvent r ((r : ℝ) • (v : Lp ℝ 2 μ) -
    S.generator ⟨v, hdom v.property⟩) = (v : Lp ℝ 2 μ) at hres
  rw [hres] at hp
  exact sub_nonneg.mp hp

/-- A bounded generator shift yields the corresponding shifted resolvent order. -/
theorem u7_shifted_resolvent_order_of_generator_order
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S T : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (Lp ℝ 2 μ))
    (hS : ∀ (t : ℝ≥0) (f : Lp ℝ 2 μ), 0 ≤ f → 0 ≤ S t f)
    (hT : ∀ (t : ℝ≥0) (f : Lp ℝ 2 μ), 0 ≤ f → 0 ≤ T t f)
    (C : ℝ) (hC : 0 ≤ C)
    (hdom : T.generatorDomain ≤ S.generatorDomain)
    (hgen : ∀ (v : T.generatorDomain) (_hv : 0 ≤ (v : Lp ℝ 2 μ)),
      T.generator v ≤ S.generator ⟨v, hdom v.property⟩ + C • (v : Lp ℝ 2 μ))
    (q : MarkovProcess.Semigroup.PositiveShift) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
    let r : MarkovProcess.Semigroup.PositiveShift := ⟨(q : ℝ) + C, add_pos_of_pos_of_nonneg q.property hC⟩
    T.resolvent r f ≤ S.resolvent q f := by
  let r : MarkovProcess.Semigroup.PositiveShift := ⟨(q : ℝ) + C, add_pos_of_pos_of_nonneg q.property hC⟩
  let v : T.generatorDomain := ⟨T.resolvent r f, T.resolvent_mem_generatorDomain r f⟩
  have hv : 0 ≤ (v : Lp ℝ 2 μ) := u7_positive_semigroup_resolvent_positive μ T hT r f hf
  have hi : (q : ℝ) • (v : Lp ℝ 2 μ) - S.generator ⟨v, hdom v.property⟩ ≤ f := by
    have ht := T.generator_resolvent r f
    have hg := hgen v hv
    have he : (q : ℝ) • (v : Lp ℝ 2 μ) - S.generator ⟨v, hdom v.property⟩ ≤
        (r : ℝ) • (v : Lp ℝ 2 μ) - T.generator v := by
      change _ ≤ ((q : ℝ) + C) • (v : Lp ℝ 2 μ) - T.generator v
      rw [add_smul]
      have h := sub_le_sub_left hg ((q : ℝ) • (v : Lp ℝ 2 μ) + C • (v : Lp ℝ 2 μ))
      convert h using 1 <;> abel
    calc
      _ ≤ (r : ℝ) • (v : Lp ℝ 2 μ) - T.generator v := he
      _ = f := by dsimp only [v]; rw [ht]; abel
  have hp : 0 ≤ S.resolvent q (f - ((q : ℝ) • (v : Lp ℝ 2 μ) -
      S.generator ⟨v, hdom v.property⟩)) :=
    u7_positive_semigroup_resolvent_positive μ S hS q _ (sub_nonneg.mpr hi)
  rw [map_sub] at hp
  have hres := S.resolvent_smul_sub_generator q ⟨(v : Lp ℝ 2 μ), hdom v.property⟩
  change S.resolvent q ((q : ℝ) • (v : Lp ℝ 2 μ) -
    S.generator ⟨v, hdom v.property⟩) = (v : Lp ℝ 2 μ) at hres
  rw [hres] at hp
  exact sub_nonneg.mp hp

#print axioms u7_shifted_resolvent_order_of_generator_order

/-- Discount a contraction semigroup by a nonnegative exponential rate. -/
noncomputable def u7DiscountedSemigroup {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (T : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (C : ℝ) (hC : 0 ≤ C) :
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E where
  operator t := Real.exp (-C * (t : ℝ)) • T t
  operator_zero := by simp
  operator_add s t := by
    ext x
    simp only [NNReal.coe_add, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.comp_apply, map_smul, T.add_apply, smul_smul]
    rw [← Real.exp_add]
    congr 2
    ring
  opNorm_le_one t := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    have he : Real.exp (-C * (t : ℝ)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hC) t.coe_nonneg
    calc
      Real.exp (-C * (t : ℝ)) * ‖T t‖ ≤ Real.exp (-C * (t : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left (T.opNorm_le_one t) (Real.exp_nonneg _)
      _ ≤ 1 := by simpa using he
  continuous_orbit x := by
    change Continuous (fun t : ℝ≥0 => Real.exp (-C * (t : ℝ)) • T t x)
    convert (Real.continuous_exp.comp (continuous_const.mul NNReal.continuous_coe)).smul
      (T.continuous_orbit x) using 1
    ext t
    rfl

/-- The resolvent of the discounted semigroup is the shifted resolvent. -/
theorem u7_discounted_resolvent {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (T : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (C : ℝ) (hC : 0 ≤ C) (q : MarkovProcess.Semigroup.PositiveShift) (f : E) :
    (u7DiscountedSemigroup T C hC).resolvent q f =
      T.resolvent ⟨(q : ℝ) + C, add_pos_of_pos_of_nonneg q.property hC⟩ f := by
  rw [MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.resolvent_apply,
    MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.resolvent_apply]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  simp only [MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.laplaceIntegrand_apply,
    u7DiscountedSemigroup, ContinuousLinearMap.smul_apply, smul_smul,
    Real.coe_toNNReal _ (le_of_lt ht)]
  rw [← Real.exp_add]
  congr 2
  ring

/-- A shifted resolvent order bounds one positive semigroup by the other. -/
theorem u7_semigroup_comparison_of_shifted_resolvent_order
    {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (S T : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup (Lp ℝ 2 μ))
    (hS : ∀ (t : ℝ≥0) (f : Lp ℝ 2 μ), 0 ≤ f → 0 ≤ S t f)
    (hT : ∀ (t : ℝ≥0) (f : Lp ℝ 2 μ), 0 ≤ f → 0 ≤ T t f)
    (C : ℝ) (hC : 0 ≤ C)
    (hR : ∀ (q : MarkovProcess.Semigroup.PositiveShift) (f : Lp ℝ 2 μ),
      0 ≤ f → T.resolvent ⟨(q : ℝ) + C, add_pos_of_pos_of_nonneg q.property hC⟩ f ≤ S.resolvent q f)
    (t : ℝ≥0) (f : Lp ℝ 2 μ) (hf : 0 ≤ f) :
    T t f ≤ Real.exp (C * (t : ℝ)) • S t f := by
  let U := u7DiscountedSemigroup T C hC
  have hU : ∀ (s : ℝ≥0) (v : Lp ℝ 2 μ), 0 ≤ v → 0 ≤ U s v := by
    intro s v hv
    exact smul_nonneg (Real.exp_nonneg _) (hT s v hv)
  have hUR (q : MarkovProcess.Semigroup.PositiveShift) (v : Lp ℝ 2 μ) (hv : 0 ≤ v) :
      U.resolvent q v ≤ S.resolvent q v := by
    rw [u7_discounted_resolvent]
    exact hR q v hv
  have h := u7_semigroup_comparison_of_resolvent_order μ S U hS hU hUR t f hf
  have h' := smul_le_smul_of_nonneg_left h (Real.exp_nonneg (C * (t : ℝ)))
  change Real.exp (C * (t : ℝ)) • (Real.exp (-C * (t : ℝ)) • T t f) ≤ _ at h'
  rw [smul_smul, ← Real.exp_add] at h'
  convert h' using 1 <;> simp

#print axioms u7_semigroup_comparison_of_shifted_resolvent_order


#print axioms u7_positive_semigroup_resolvent_positive
#print axioms u7_resolvent_order_of_generator_order


open EinsteinRelation.SpatialDirichlet

noncomputable section

/-- The signed reversible measure is the unforced reversible measure weighted
by the square of the exponential gauge. -/
theorem u7_physical_reversible_measure_gauge {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) :
    physicalReversibleMeasure ω hd lam =
      (physicalReversibleMeasure ω hd 0).withDensity
        (fun x => ENNReal.ofReal (Real.exp (2 * lam * x (firstCoordinateIndex hd)))) := by
  have h0 : Measurable (fun x : Vec d => ENNReal.ofReal (sourcePhysicalDensity ω hd 0 x)) :=
    (continuousSourcePhysicalDensity ω hd 0).measurable.ennreal_ofReal
  have hw : Measurable (fun x : Vec d => ENNReal.ofReal
      (Real.exp (2 * lam * x (firstCoordinateIndex hd)))) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _))).measurable.ennreal_ofReal
  change volume.withDensity (fun x => ENNReal.ofReal (sourcePhysicalDensity ω hd lam x)) =
    (volume.withDensity (fun x => ENNReal.ofReal (sourcePhysicalDensity ω hd 0 x))).withDensity _
  rw [← withDensity_mul volume h0 hw]
  congr 1
  funext x
  simp only [Pi.mul_apply, ← ENNReal.ofReal_mul (positiveSourcePhysicalDensity ω hd 0 x).le]
  congr 1
  simp only [sourcePhysicalDensity, sourceForceWeight, firstCoordinateIndex, mul_zero, zero_mul, Real.exp_zero, one_mul]
  ring

#print axioms u7_physical_reversible_measure_gauge

/-- Multiplication by the exponential gauge preserves the actual physical L²
norm, including the reversible clock weight. -/
theorem u7_physical_gauge_eLpNorm {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (f : Vec d → ℝ)
    (hf : AEStronglyMeasurable f (physicalReversibleMeasure ω hd lam)) :
    eLpNorm (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) 2
      (physicalReversibleMeasure ω hd 0) =
      eLpNorm f 2 (physicalReversibleMeasure ω hd lam) := by
  have hvol : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd lam := by
    apply Measure.ae_le_iff_absolutelyContinuous.mp
    intro P hP
    exact (Blueprint.gmpPhysical_ae_iff_volume hd ω lam P).mp hP
  have hzero : physicalReversibleMeasure ω hd 0 ≪ (volume : Measure (Vec d)) :=
    withDensity_absolutelyContinuous _ _
  have hg : AEStronglyMeasurable (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x)
      (physicalReversibleMeasure ω hd 0) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _))).aestronglyMeasurable.mul
      (hf.mono_ac (hzero.trans hvol))
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hg,
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num : (2 : ℝ≥0∞) ≠ 0)
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞) hf]
  congr 1
  rw [u7_physical_reversible_measure_gauge hd ω lam,
    lintegral_withDensity_eq_lintegral_mul_non_measurable _
      (show Measurable (fun x : Vec d => ENNReal.ofReal
        (Real.exp (2 * lam * x (firstCoordinateIndex hd)))) from
        (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _))).measurable.ennreal_ofReal)
      (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)]
  apply lintegral_congr
  intro x
  simp only [enorm_mul, ENNReal.toReal_ofNat]
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)]
  congr 1
  rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), ENNReal.rpow_two,
    ← ENNReal.ofReal_pow (Real.exp_pos _).le, ← Real.exp_nat_mul]
  congr 1
  ring

#print axioms u7_physical_gauge_eLpNorm

/-- The exponential gauge sends actual signed physical L² functions into the
unforced physical L² space. -/
theorem u7_physical_gauge_memLp {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) {f : Vec d → ℝ} (hf : MemLp f 2 (physicalReversibleMeasure ω hd lam)) :
    MemLp (fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x) 2
      (physicalReversibleMeasure ω hd 0) := by
  rw [memLp_iff]
  rw [u7_physical_gauge_eLpNorm hd ω lam f hf.aestronglyMeasurable]
  exact hf

#print axioms u7_physical_gauge_memLp

/-- The inverse exponential gauge sends unforced physical L² functions to the
signed physical L² space. -/
theorem u7_physical_inverse_gauge_memLp {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) {f : Vec d → ℝ} (hf : MemLp f 2 (physicalReversibleMeasure ω hd 0)) :
    MemLp (fun x => Real.exp (-lam * x (firstCoordinateIndex hd)) * f x) 2
      (physicalReversibleMeasure ω hd lam) := by
  have hvol : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd 0 := by
    apply Measure.ae_le_iff_absolutelyContinuous.mp
    intro P hP
    exact (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 P).mp hP
  have hsigned : physicalReversibleMeasure ω hd lam ≪ (volume : Measure (Vec d)) :=
    withDensity_absolutelyContinuous _ _
  have hg : AEStronglyMeasurable
      (fun x => Real.exp (-lam * x (firstCoordinateIndex hd)) * f x)
      (physicalReversibleMeasure ω hd lam) :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _))).aestronglyMeasurable.mul
      (hf.aestronglyMeasurable.mono_ac (hsigned.trans hvol))
  rw [memLp_iff]
  have he := u7_physical_gauge_eLpNorm hd ω lam
    (fun x => Real.exp (-lam * x (firstCoordinateIndex hd)) * f x) hg
  have hid : (fun x : Vec d => Real.exp (lam * x (firstCoordinateIndex hd)) *
      (Real.exp (-lam * x (firstCoordinateIndex hd)) * f x)) = f := by
    funext x
    rw [← mul_assoc, ← Real.exp_add]
    simp
  rw [hid] at he
  rw [← he]
  exact hf

#print axioms u7_physical_inverse_gauge_memLp

private def u7PhysicalGaugeLp {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd 0) :=
  (u7_physical_gauge_memLp hd ω lam (Lp.memLp f)).toLp _

private theorem u7PhysicalGaugeLp_coe {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (u7PhysicalGaugeLp hd ω lam f : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd 0]
      fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x :=
  MemLp.coeFn_toLp _

private def u7PhysicalGaugeIsometry {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) →ₗᵢ[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd 0) where
  toFun := u7PhysicalGaugeLp hd ω lam
  map_add' f g := by
    apply Lp.ext
    have hac : physicalReversibleMeasure ω hd 0 ≪ physicalReversibleMeasure ω hd lam := by
      apply Measure.ae_le_iff_absolutelyContinuous.mp
      intro P hP
      exact (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 P).mpr
        ((Blueprint.gmpPhysical_ae_iff_volume hd ω lam P).mp hP)
    filter_upwards [u7PhysicalGaugeLp_coe hd ω lam (f + g),
      u7PhysicalGaugeLp_coe hd ω lam f, u7PhysicalGaugeLp_coe hd ω lam g,
      Lp.coeFn_add (u7PhysicalGaugeLp hd ω lam f) (u7PhysicalGaugeLp hd ω lam g),
      hac.ae_eq (Lp.coeFn_add f g)] with x hsum hf hg hout hin
    rw [hsum, hout]
    simp only [Pi.add_apply]
    rw [hf, hg, hin]
    simp only [Pi.add_apply, mul_add]
  map_smul' c f := by
    apply Lp.ext
    have hac : physicalReversibleMeasure ω hd 0 ≪ physicalReversibleMeasure ω hd lam := by
      apply Measure.ae_le_iff_absolutelyContinuous.mp
      intro P hP
      exact (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 P).mpr
        ((Blueprint.gmpPhysical_ae_iff_volume hd ω lam P).mp hP)
    filter_upwards [u7PhysicalGaugeLp_coe hd ω lam (c • f), u7PhysicalGaugeLp_coe hd ω lam f,
      Lp.coeFn_smul c (u7PhysicalGaugeLp hd ω lam f), hac.ae_eq (Lp.coeFn_smul c f)]
      with x hcf hf hout hin
    simp only [RingHom.id_apply]
    rw [hcf, hout]
    simp only [Pi.smul_apply]
    rw [hf, hin]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  norm_map' f := by
    change ‖(u7_physical_gauge_memLp hd ω lam (Lp.memLp f)).toLp _‖ = _
    rw [Lp.norm_toLp, u7_physical_gauge_eLpNorm hd ω lam _ (Lp.memLp f).aestronglyMeasurable, Lp.norm_def]

private theorem u7PhysicalGaugeIsometry_surjective {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ) : Function.Surjective (u7PhysicalGaugeIsometry hd ω lam) := by
  intro f
  let hf := u7_physical_inverse_gauge_memLp hd ω lam (Lp.memLp f)
  refine ⟨hf.toLp _, Lp.ext ?_⟩
  have hac : physicalReversibleMeasure ω hd 0 ≪ physicalReversibleMeasure ω hd lam := by
    apply Measure.ae_le_iff_absolutelyContinuous.mp
    intro P hP
    exact (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 P).mpr
      ((Blueprint.gmpPhysical_ae_iff_volume hd ω lam P).mp hP)
  have hrep := hac.ae_eq hf.coeFn_toLp
  filter_upwards [u7PhysicalGaugeLp_coe hd ω lam (hf.toLp _), hrep] with x hout hin
  change u7PhysicalGaugeLp hd ω lam (hf.toLp _) x = f x
  rw [hout, hin, ← mul_assoc, ← Real.exp_add]
  simp

/-- The exponential gauge is an isometric equivalence between the actual real
signed and unforced physical L² spaces. -/
def u7PhysicalGaugeUnitary {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ) :
    Lp ℝ 2 (physicalReversibleMeasure ω hd lam) ≃ₗᵢ[ℝ]
      Lp ℝ 2 (physicalReversibleMeasure ω hd 0) :=
  LinearIsometryEquiv.ofSurjective (u7PhysicalGaugeIsometry hd ω lam)
    (u7PhysicalGaugeIsometry_surjective hd ω lam)

/-- The physical L² gauge acts by the actual exponential multiplier. -/
theorem u7_physical_gauge_unitary_coe {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    (u7PhysicalGaugeUnitary hd ω lam f : Vec d → ℝ) =ᵐ[physicalReversibleMeasure ω hd 0]
      fun x => Real.exp (lam * x (firstCoordinateIndex hd)) * f x :=
  u7PhysicalGaugeLp_coe hd ω lam f

#print axioms u7_physical_gauge_unitary_coe

/-- The inverse physical L² gauge multiplies by the inverse exponential. -/
theorem u7_physical_gauge_unitary_symm_coe {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)) :
    ((u7PhysicalGaugeUnitary hd ω lam).symm f : Vec d → ℝ) =ᵐ[
      physicalReversibleMeasure ω hd lam]
      fun x => Real.exp (-lam * x (firstCoordinateIndex hd)) * f x := by
  have h := u7_physical_gauge_unitary_coe hd ω lam ((u7PhysicalGaugeUnitary hd ω lam).symm f)
  have h' := (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mpr
    ((Blueprint.gmpPhysical_ae_iff_volume hd ω 0 _).mp h)
  filter_upwards [h'] with x hx
  simp only [LinearIsometryEquiv.apply_symm_apply] at hx
  rw [hx, ← mul_assoc, ← Real.exp_add]
  simp

#print axioms u7_physical_gauge_unitary_symm_coe

/-- The physical exponential gauge and its inverse preserve positivity. -/
theorem u7_physical_gauge_unitary_positive {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) (hf : 0 ≤ f) :
    0 ≤ u7PhysicalGaugeUnitary hd ω lam f := by
  apply (Lp.coeFn_nonneg _).mp
  have h := (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 _).mpr
    ((Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp ((Lp.coeFn_nonneg _).mpr hf))
  filter_upwards [u7_physical_gauge_unitary_coe hd ω lam f, h] with x hx hfx
  rw [hx]
  exact mul_nonneg (Real.exp_nonneg _) hfx

/-- The inverse physical exponential gauge preserves positivity. -/
theorem u7_physical_gauge_unitary_symm_positive {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)) (hf : 0 ≤ f) :
    0 ≤ (u7PhysicalGaugeUnitary hd ω lam).symm f := by
  apply (Lp.coeFn_nonneg _).mp
  have h := (Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mpr
    ((Blueprint.gmpPhysical_ae_iff_volume hd ω 0 _).mp ((Lp.coeFn_nonneg _).mpr hf))
  filter_upwards [u7_physical_gauge_unitary_symm_coe hd ω lam f, h] with x hx hfx
  rw [hx]
  exact mul_nonneg (Real.exp_nonneg _) hfx

#print axioms u7_physical_gauge_unitary_positive
#print axioms u7_physical_gauge_unitary_symm_positive

/-- On compact continuous inputs the physical gauge gives the expected weighted test. -/
theorem u7_physical_gauge_unitary_compact_test {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (f : Vec d → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    let g := fun y => Real.exp (lam * y (firstCoordinateIndex hd)) * f y
    let hg : Continuous g :=
      (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _))).mul hf
    let hgc : HasCompactSupport g := hfc.mul_left
    u7PhysicalGaugeUnitary hd ω lam
      ((Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc).toLp f) =
        (Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 g hg hgc).toLp g := by
  let g : Vec d → ℝ := fun y => Real.exp (lam * y (firstCoordinateIndex hd)) * f y
  have hg : Continuous g :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _))).mul hf
  have hgc : HasCompactSupport g := hfc.mul_left
  let F := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc
  let G := Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 g hg hgc
  change u7PhysicalGaugeUnitary hd ω lam (F.toLp f) = G.toLp g
  apply Lp.ext
  have hF := (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 _).mpr
    ((Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp F.coeFn_toLp)
  filter_upwards [u7_physical_gauge_unitary_coe hd ω lam (F.toLp f), hF, G.coeFn_toLp]
    with x hx hf' hg'
  rw [hx, hf', hg']


/-- Pointwise physical-kernel domination follows from actual gauged L² order. -/
theorem u7_regular_gauge_domination_of_physical_L2_order {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (t : ℝ≥0) (C : ℝ)
    (horder : ∀ f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam), 0 ≤ f →
      u7PhysicalGaugeUnitary hd ω lam
        (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t f) ≤
      Real.exp (C * (t : ℝ)) •
        Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (u7PhysicalGaugeUnitary hd ω lam f)) :
    ∀ (x : Vec d) (s : Set (Vec d)), MeasurableSet s →
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x s ≤
        ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
          ∫⁻ y in s, ENNReal.ofReal (Real.exp (lam * ((y - x) (firstCoordinateIndex hd))))
            ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x := by
  apply u7_regular_gauge_domination_of_physical_gauge_comparison hd ω lam Λ hΛ hω t C
  intro f hf hfc hfn
  let g : Vec d → ℝ := fun y => Real.exp (lam * y (firstCoordinateIndex hd)) * f y
  have hg : Continuous g :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_apply _))).mul hf
  have hgc : HasCompactSupport g := hfc.mul_left
  let F := Blueprint.gmpPhysical_compactContinuous_memLp hd ω lam f hf hfc
  let G := Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 g hg hgc
  have hF : 0 ≤ F.toLp f := (Lp.coeFn_nonneg _).mp <| F.coeFn_toLp.mono fun x hx => by
    rw [hx]; exact hfn x
  have hG : u7PhysicalGaugeUnitary hd ω lam (F.toLp f) = G.toLp g :=
    u7_physical_gauge_unitary_compact_test hd ω lam f hf hfc
  have hlp := horder (F.toLp f) hF
  rw [hG] at hlp
  have hle := (Lp.coeFn_le _ _).mpr hlp
  have hmul := Lp.coeFn_smul (Real.exp (C * (t : ℝ)))
    (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (G.toLp g))
  have hgauge := u7_physical_gauge_unitary_coe hd ω lam
    (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t (F.toLp f))
  have hv := (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 _).mp
    (hle.and (hmul.and hgauge))
  filter_upwards [hv] with x hx
  rcases hx with ⟨hle, hmul, hgauge⟩
  rw [hmul, hgauge] at hle
  simp only [Pi.smul_apply, smul_eq_mul] at hle
  have h := mul_le_mul_of_nonneg_left hle (Real.exp_nonneg (-lam * x (firstCoordinateIndex hd)))
  rw [← mul_assoc, ← Real.exp_add] at h
  simp only [neg_mul, neg_add_cancel, Real.exp_zero, one_mul] at h
  rw [← mul_assoc, ← Real.exp_add] at h
  convert h using 1 <;> congr 2 <;> ring


#print axioms u7_regular_gauge_domination_of_physical_L2_order

/-- Full generator-domain order yields the physical kernel gauge comparison. -/
theorem u7_regular_gauge_domination_of_conjugated_generator_order {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) (C : ℝ) (hC : 0 ≤ C)
    (hdom : (u7ConjugatedSemigroup (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω)
      (u7PhysicalGaugeUnitary hd ω lam)).generatorDomain ≤
        (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω).generatorDomain)
    (hgen : ∀ v : (u7ConjugatedSemigroup
        (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω)
        (u7PhysicalGaugeUnitary hd ω lam)).generatorDomain,
      0 ≤ (v : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)) →
      (u7ConjugatedSemigroup (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω)
        (u7PhysicalGaugeUnitary hd ω lam)).generator v ≤
      (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω).generator ⟨v, hdom v.property⟩ +
        C • (v : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)))
    (t : ℝ≥0) :
    ∀ (x : Vec d) (s : Set (Vec d)), MeasurableSet s →
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x s ≤
        ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
          ∫⁻ y in s, ENNReal.ofReal (Real.exp (lam * ((y - x) (firstCoordinateIndex hd))))
            ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x := by
  let S := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
  let T := u7ConjugatedSemigroup (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω)
    (u7PhysicalGaugeUnitary hd ω lam)
  have hS : ∀ (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)),
      0 ≤ f → 0 ≤ S t f := by
    intro t f hf
    apply (Lp.coeFn_nonneg _).mp
    exact Blueprint.gmpPhysicalSemigroup_positive hd ω 0 Λ hΛ hω t
      ((Lp.coeFn_nonneg f).mpr hf)
  have hT : ∀ (t : ℝ≥0) (f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)),
      0 ≤ f → 0 ≤ T t f := by
    apply u7_conjugated_semigroup_positive _ _ _ _
    · exact u7_physical_gauge_unitary_positive hd ω lam
    · exact u7_physical_gauge_unitary_symm_positive hd ω lam
    · intro t f hf
      apply (Lp.coeFn_nonneg _).mp
      exact Blueprint.gmpPhysicalSemigroup_positive hd ω lam Λ hΛ hω t
        ((Lp.coeFn_nonneg f).mpr hf)
  apply u7_regular_gauge_domination_of_physical_L2_order hd ω lam Λ hΛ hω t C
  intro f hf
  have h := u7_semigroup_comparison_of_shifted_resolvent_order
    (physicalReversibleMeasure ω hd 0) S T hS hT C hC
      (fun q g hg => u7_shifted_resolvent_order_of_generator_order
        (physicalReversibleMeasure ω hd 0) S T hS hT C hC hdom hgen q g hg)
      t (u7PhysicalGaugeUnitary hd ω lam f)
      (u7_physical_gauge_unitary_positive hd ω lam f hf)
  change u7PhysicalGaugeUnitary hd ω lam
    (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω t
      ((u7PhysicalGaugeUnitary hd ω lam).symm (u7PhysicalGaugeUnitary hd ω lam f))) ≤
    Real.exp (C * (t : ℝ)) •
      Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (u7PhysicalGaugeUnitary hd ω lam f) at h
  rw [LinearIsometryEquiv.symm_apply_apply] at h
  exact h

#print axioms u7_regular_gauge_domination_of_conjugated_generator_order


/-- The actual signed regular physical kernel is absolutely continuous at
positive times for every starting point. -/
theorem u7_regular_signed_kernel_absolutelyContinuous
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) :
    ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x ≪
      (volume : Measure (Vec d)) := by
  apply u7_regular_signed_kernel_ac_of_local_L2_bound hd ω lam Λ hΛ hω t
  intro x
  exact u4_regular_signed_kernel_local_L2_bound hd ω lam Λ hΛ hω t ht x

#print axioms u7_regular_signed_kernel_absolutelyContinuous

/-- The signed regular physical kernel has a jointly measurable normalized
real density at every positive time. -/
theorem u7_regular_signed_kernel_normalized_density
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) :
    ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
      (∀ x y, 0 ≤ p x y) ∧
      (∀ x, Integrable (p x) volume ∧ ∫ y, p x y = 1) ∧
      ∀ x, u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x =
        volume.withDensity (fun y => ENNReal.ofReal (p x y)) :=
  u7_regular_signed_kernel_normalized_density_of_absolutelyContinuous
    hd ω lam Λ hΛ hω t
    (u7_regular_signed_kernel_absolutelyContinuous hd ω lam Λ hΛ hω t ht)

#print axioms u7_regular_signed_kernel_normalized_density

end

end EinsteinFull

namespace EinsteinFull

/-- A row-wise measure bound by a jointly measurable nonnegative envelope
allows the density to be clipped simultaneously for all starting points. -/
theorem u7_real_density_clipped_of_domination {d : ℕ}
    (K : Kernel (Vec d) (Vec d)) (p b : Vec d → Vec d → ℝ)
    (hp : Measurable (Function.uncurry p))
    (hb : Measurable (Function.uncurry b))
    (hp0 : ∀ x y, 0 ≤ p x y) (hb0 : ∀ x y, 0 ≤ b x y)
    (hrep : ∀ x, K x = (volume : Measure (Vec d)).withDensity
      (fun y => ENNReal.ofReal (p x y)))
    (hdom : ∀ x, K x ≤ (volume : Measure (Vec d)).withDensity
      (fun y => ENNReal.ofReal (b x y))) :
    ∃ q : Vec d → Vec d → ℝ, Measurable (Function.uncurry q) ∧
      (∀ x y, 0 ≤ q x y ∧ q x y ≤ b x y) ∧
      ∀ x, K x = (volume : Measure (Vec d)).withDensity
        (fun y => ENNReal.ofReal (q x y)) := by
  refine ⟨fun x y => min (p x y) (b x y), hp.min hb, ?_, ?_⟩
  · intro x y
    exact ⟨le_min (hp0 x y) (hb0 x y), min_le_right _ _⟩
  · intro x
    have hpx : Measurable (p x) := hp.comp (measurable_const.prodMk measurable_id)
    have hae : (fun y => ENNReal.ofReal (p x y)) ≤ᵐ[volume]
        (fun y => ENNReal.ofReal (b x y)) := by
      apply ae_le_of_forall_setLIntegral_le_of_sigmaFinite₀ hpx.ennreal_ofReal.aemeasurable
      intro s hs _
      rw [← withDensity_apply _ hs, ← withDensity_apply _ hs, ← hrep x]
      exact Measure.le_iff.mp (hdom x) s hs
    rw [hrep x]
    apply withDensity_congr_ae
    filter_upwards [hae] with y hy
    have hle : p x y ≤ b x y := (ENNReal.ofReal_le_ofReal_iff (hb0 x y)).mp hy
    simp only [min_eq_left hle]

#print axioms u7_real_density_clipped_of_domination

end EinsteinFull

namespace EinsteinFull

/-- Conjugation also reflects the full generator graph. -/
theorem u7_conjugated_semigroup_generator_inverse {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (T : MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup E)
    (U : E ≃ₗᵢ[ℝ] F) (v : (u7ConjugatedSemigroup T U).generatorDomain) :
    ∃ hv : U.symm v ∈ T.generatorDomain,
      T.generator ⟨U.symm v, hv⟩ = U.symm ((u7ConjugatedSemigroup T U).generator v) := by
  let S := u7ConjugatedSemigroup T U
  have h : Filter.Tendsto (T.differenceQuotient (U.symm v)) (𝓝[>] 0)
      (𝓝 (U.symm (S.generator v))) := by
    have ht := U.symm.continuous.tendsto (S.generator v) |>.comp (S.tendsto_generator v)
    convert ht using 1
    ext t
    change T.differenceQuotient (U.symm v) t =
      U.symm ((t : ℝ)⁻¹ • (U (T t (U.symm v)) - v))
    rw [map_smul, map_sub, U.symm_apply_apply]
    rfl
  refine ⟨T.mem_generatorDomain_of_tendsto h, ?_⟩
  exact T.generator_eq_of_tendsto _ h

#print axioms u7_conjugated_semigroup_generator_inverse

end EinsteinFull

namespace EinsteinFull

/-- The physical L² exponential gauge transports the complete H¹ domain. -/
theorem u7_physical_gauge_unitary_H1_iff {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ)
    (f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    physicalH1Member ω hd lam f ↔ physicalH1Member ω hd 0
      (u7PhysicalGaugeUnitary hd ω lam f) := by
  rw [u2_regular_physical_H1_gauge_iff hd ω lam f]
  have h := u7_physical_gauge_unitary_coe hd ω lam f
  constructor
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.trans h.symm⟩
  · rintro ⟨q, hq⟩
    exact ⟨q, hq.trans h⟩

#print axioms u7_physical_gauge_unitary_H1_iff

/-- The physical L² gauge agrees with the full H¹ gauge on every graph value. -/
theorem u7_physical_gauge_unitary_H1_value {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hω : IsRegular Λ ω) (u : PhysicalH1Space hd lam) :
    u7PhysicalGaugeUnitary hd ω lam (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω u) =
      Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam u) := by
  apply Lp.ext
  have hi := (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 _).mpr
    ((Blueprint.gmpPhysical_ae_iff_volume hd ω lam _).mp
      (Blueprint.gmpPhysicalH1Value_ae_eq hd ω lam Λ hω u))
  have hg := (Blueprint.gmpPhysical_ae_iff_volume hd ω 0 _).mpr
    (u2PhysicalH1Gauge_value_ae hd lam u)
  filter_upwards [u7_physical_gauge_unitary_coe hd ω lam
      (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω u), hi, hg,
      Blueprint.gmpPhysicalH1Value_ae_eq hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam u)]
      with x hU hI hG hO
  rw [hU, hI, hO]
  exact hG.symm

#print axioms u7_physical_gauge_unitary_H1_value

end EinsteinFull


namespace EinsteinFull

/-- The full physical closed form transforms by the actual bounded potential. -/
theorem u7_physical_gauge_full_closedForm {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (u v : PhysicalH1Space hd lam) :
    (Blueprint.gmpPhysicalClosedForm hd ω lam Λ hΛ hω).form
      (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω u)
      (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v) =
    (Blueprint.gmpPhysicalClosedForm hd ω 0 Λ hΛ hω).form
      (u7PhysicalGaugeUnitary hd ω lam (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω u))
      (u7PhysicalGaugeUnitary hd ω lam (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v)) +
    inner ℝ (u2PhysicalGaugePotentialMul hd ω lam Λ hΛ hω
      (u7PhysicalGaugeUnitary hd ω lam (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω u)))
      (u7PhysicalGaugeUnitary hd ω lam (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v)) := by
  rw [u7_physical_gauge_unitary_H1_value hd ω lam Λ hω u,
      u7_physical_gauge_unitary_H1_value hd ω lam Λ hω v]
  change Blueprint.gmpPhysicalH1Form hd ω lam Λ hω
      (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω u)
      (Blueprint.gmpPhysicalH1Value hd ω lam Λ hω v) =
    Blueprint.gmpPhysicalH1Form hd ω 0 Λ hω
      (Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam u))
      (Blueprint.gmpPhysicalH1Value hd ω 0 Λ hω (u2PhysicalH1Gauge hd lam v)) + _
  rw [Blueprint.gmpPhysicalH1Form_value hd ω lam Λ hω u v,
    Blueprint.gmpPhysicalH1Form_value hd ω 0 Λ hω
      (u2PhysicalH1Gauge hd lam u) (u2PhysicalH1Gauge hd lam v)]
  exact u2_regular_gauge_full_form hd ω lam Λ hΛ hω u v

#print axioms u7_physical_gauge_full_closedForm

/-- The actual physical potential has a uniform lower bound on positive L² inputs. -/
theorem u7_physical_gauge_potential_mul_order {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0),
      0 ≤ f → -u2PhysicalGaugePotentialMul hd ω lam Λ hΛ hω f ≤ C • f := by
  obtain ⟨_, C, hC, hbound⟩ :=
    u2_regular_physical_gauge_potential_bounded ω lam Λ hΛ hω (firstCoordinateIndex hd)
  refine ⟨C, hC, ?_⟩
  intro f hf
  apply (Lp.coeFn_le _ _).mp
  filter_upwards [Lp.coeFn_neg (u2PhysicalGaugePotentialMul hd ω lam Λ hΛ hω f),
    Lp.coeFn_smul C f, u2PhysicalGaugePotentialMul_coe hd ω lam Λ hΛ hω f,
    (Lp.coeFn_nonneg f).mpr hf] with x hn hs hm hfx
  rw [hn, hs]
  simp only [Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
  rw [hm]
  have hv : -(lam * physicalDrift ω (firstCoordinateIndex hd) 0 x
        (firstCoordinateIndex hd) + (lam ^ 2 / 2) * ω.1 x
        (firstCoordinateIndex hd) (firstCoordinateIndex hd)) ≤ C :=
    (neg_le_abs _).trans (hbound x)
  simpa only [neg_mul] using mul_le_mul_of_nonneg_right hv hfx

#print axioms u7_physical_gauge_potential_mul_order

/-- The actual conjugated generator is the zero-force generator minus the gauge potential. -/
theorem u7_physical_gauge_conjugated_generator_graph {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam Λ : ℝ) (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω)
    (v : (u7ConjugatedSemigroup (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω)
      (u7PhysicalGaugeUnitary hd ω lam)).generatorDomain) :
    ∃ hv : (v : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)) ∈
      (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω).generatorDomain,
      (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω).generator ⟨v, hv⟩ =
        (u7ConjugatedSemigroup (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω)
          (u7PhysicalGaugeUnitary hd ω lam)).generator v +
        u2PhysicalGaugePotentialMul hd ω lam Λ hΛ hω v := by
  let U := u7PhysicalGaugeUnitary hd ω lam
  let T := Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω
  let S := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
  let G := u7ConjugatedSemigroup T U
  obtain ⟨hf, hgen⟩ := u7_conjugated_semigroup_generator_inverse T U v
  have hfH := Blueprint.gmpPhysicalSemigroup_generator_physicalH1Member hd ω lam Λ hΛ hω
    ⟨U.symm v, hf⟩
  have hvH : physicalH1Member ω hd 0 v := by
    have h := (u7_physical_gauge_unitary_H1_iff hd ω lam (U.symm v)).mp hfH
    simpa [U] using h
  have hfRange := (Blueprint.mem_gmpPhysicalH1Domain_iff hd ω lam Λ hω (U.symm v)).mpr hfH
  change U.symm v ∈ (Blueprint.gmpPhysicalH1ValueLinear hd ω lam Λ hω).range at hfRange
  obtain ⟨u, hu⟩ := hfRange
  change Blueprint.gmpPhysicalH1Value hd ω lam Λ hω u = U.symm v at hu
  apply (Blueprint.gmpPhysicalSemigroup_generator_iff hd ω 0 Λ hΛ hω v
    (G.generator v + u2PhysicalGaugePotentialMul hd ω lam Λ hΛ hω v)).mpr
  refine ⟨hvH, ?_⟩
  intro y hy
  have hyH := (Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω 0 Λ hΛ hω y).mp hy
  have hys : physicalH1Member ω hd lam (U.symm y) := by
    apply (u7_physical_gauge_unitary_H1_iff hd ω lam (U.symm y)).mpr
    simpa [U] using hyH
  have hyRange := (Blueprint.mem_gmpPhysicalH1Domain_iff hd ω lam Λ hω (U.symm y)).mpr hys
  change U.symm y ∈ (Blueprint.gmpPhysicalH1ValueLinear hd ω lam Λ hω).range at hyRange
  obtain ⟨w, hw⟩ := hyRange
  change Blueprint.gmpPhysicalH1Value hd ω lam Λ hω w = U.symm y at hw
  have hpair := Blueprint.gmpPhysicalSemigroup_generator_form hd ω lam Λ hΛ hω
    ⟨U.symm v, hf⟩ (U.symm y)
    ((Blueprint.mem_gmpPhysicalClosedForm_domain_iff hd ω lam Λ hΛ hω _).mpr hys)
  have hform := u7_physical_gauge_full_closedForm hd ω lam Λ hΛ hω u w
  rw [hu, hw] at hform
  simp only [U, LinearIsometryEquiv.apply_symm_apply] at hform
  have hinner : inner ℝ (T.generator ⟨U.symm v, hf⟩) (U.symm y) =
      inner ℝ (G.generator v) y := by
    rw [hgen]
    change inner ℝ (U.symm (G.generator v)) (U.symm y) = inner ℝ (G.generator v) y
    exact U.symm.inner_map_map (G.generator v) y
  rw [hinner, hform] at hpair
  rw [inner_add_left]
  linarith only [hpair]

#print axioms u7_physical_gauge_conjugated_generator_graph

end EinsteinFull



namespace EinsteinFull

/-- A potential lower bound gives the corresponding generator upper bound. -/
theorem u7_add_order_of_generator_eq {E : Type*} [AddCommGroup E] [PartialOrder E]
    [IsOrderedAddMonoid E] {A B V P : E} (h : A = B + V) (hp : -V ≤ P) : B ≤ A + P := by
  calc
    B = (B + V) + -V := by abel
    _ ≤ (B + V) + P := by simpa only [add_comm] using add_le_add_left hp (B + V)
    _ = A + P := congrArg (fun z => z + P) h.symm

/-- Every-start signed kernel comparison for the actual physical gauge. -/
theorem u7_regular_signed_kernel_gauge_domination
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0) (x : Vec d) (s : Set (Vec d)),
      MeasurableSet s →
      u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x s ≤
        ENNReal.ofReal (Real.exp (C * (t : ℝ))) *
          ∫⁻ y in s,
            ENNReal.ofReal (Real.exp (lam * ((y - x) ⟨0, by omega⟩)))
            ∂u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x := by
  obtain ⟨C, hC, hpotential⟩ := u7_physical_gauge_potential_mul_order hd ω lam Λ hΛ hω
  let T := u7ConjugatedSemigroup (Blueprint.gmpPhysicalSemigroup hd ω lam Λ hΛ hω)
    (u7PhysicalGaugeUnitary hd ω lam)
  let S := Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
  have hdom : T.generatorDomain ≤ S.generatorDomain := by
    intro v hv
    exact (u7_physical_gauge_conjugated_generator_graph hd ω lam Λ hΛ hω ⟨v, hv⟩).choose
  have hgen : ∀ v : T.generatorDomain, 0 ≤ (v : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)) →
      T.generator v ≤ S.generator ⟨v, hdom v.property⟩ + C • (v : Lp ℝ 2 (physicalReversibleMeasure ω hd 0)) := by
    intro v hv
    have he := (u7_physical_gauge_conjugated_generator_graph hd ω lam Λ hΛ hω v).choose_spec
    have hp := hpotential v hv
    have he' : S.generator ⟨v, hdom v.property⟩ =
        T.generator v + u2PhysicalGaugePotentialMul hd ω lam Λ hΛ hω v := by
      exact he
    exact u7_add_order_of_generator_eq he' hp
  refine ⟨C, hC, ?_⟩
  intro t x s hs
  simpa [firstCoordinateIndex] using
    u7_regular_gauge_domination_of_conjugated_generator_order hd ω lam Λ hΛ hω C
      hC.le hdom hgen t x s hs

#print axioms u7_regular_signed_kernel_gauge_domination

end EinsteinFull

namespace EinsteinFull

/-- Every positive-time signed kernel row acts boundedly on the full physical L² space. -/
theorem u7_regular_signed_kernel_full_L2_integrable_bound
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) (t : ℝ≥0) (ht : 0 < t) (x : Vec d) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Lp ℝ 2 (physicalReversibleMeasure ω hd lam),
      Integrable (fun y => f y) (u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x) ∧
      |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤ C * ‖f‖ := by
  obtain ⟨C, hC, hb⟩ := u4_regular_signed_kernel_L2_integral_abs_bound
    hd ω lam Λ hΛ hω t ht (Metric.ball x 1) Metric.isOpen_ball Metric.isBounded_ball
  refine ⟨C, hC, fun f => ⟨u4_regular_signed_kernel_integrable_L2 hd ω lam Λ hΛ hω t ht f x, ?_⟩⟩
  calc
    |∫ y, f y ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x| ≤
        ∫ y, |f y| ∂u2RegularC0KernelSemigroup hd ω lam Λ hΛ hω t x := by
      simpa only [Real.norm_eq_abs] using
        norm_integral_le_integral_norm (fun y => f y)
    _ ≤ C * ‖f‖ := hb x (Metric.mem_ball_self (by norm_num)) f

#print axioms u7_regular_signed_kernel_full_L2_integrable_bound

end EinsteinFull

namespace EinsteinFull

open EinsteinRelation.SpatialDirichlet

/-- Quantitative L²-to-L∞ decay for the actual unforced physical evolution. -/
theorem u7_unforced_physical_L2_to_Linfty_decay
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t →
      ∀ f : Lp ℝ 2 (physicalReversibleMeasure ω hd 0),
        ∀ᵐ x ∂physicalReversibleMeasure ω hd 0,
          |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t f x| ≤
            C * (t : ℝ) ^ (-(d : ℝ) / 4) * ‖f‖ := by
  obtain ⟨D, hD, hdec⟩ := u7_unforced_physical_L1_to_L2 hd ω Λ hΛ hω
  let μ := physicalReversibleMeasure ω hd 0
  let K := Real.exp (2 * Λ)
  have hK : 0 < K := Real.exp_pos _
  refine ⟨D * K, mul_pos hD hK, ?_⟩
  intro t ht f
  let : SigmaFinite μ := EinsteinRelation.Diffusion.physicalReversibleMeasure_sigmaFinite hd ω 0
  have htp : 0 < (t : ℝ) := ht
  have hpow : 0 ≤ (t : ℝ) ^ (-(d : ℝ) / 4) := Real.rpow_nonneg htp.le _
  have h := u8_symmetric_L1_L2_transpose μ
    (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t)
    ((D * K) * (t : ℝ) ^ (-(d : ℝ) / 4))
    (Blueprint.gmpPhysicalSemigroup_inner_comm hd ω 0 Λ hΛ hω t) ?_ f
  · exact h
  · intro g hg1 hg2
    have hgvol : Integrable g volume := memLp_one_iff_integrable.mp <|
      (memLp_one_iff_integrable.mpr hg1).of_measure_le_smul
        (c := ENNReal.ofReal K) ENNReal.ofReal_ne_top
        (u4_unforced_physical_measure_comparable hd ω Λ hω).2
    have hmass : (∫ x, |g x|) ≤ K * (∫ x, |g x| ∂μ) := by
      apply integral_le_const_mul_of_measure_le volume μ K hK.le
        (u4_unforced_physical_measure_comparable hd ω Λ hω).2
        (fun x => |g x|) (Filter.Eventually.of_forall fun x => abs_nonneg _)
      simpa only [Real.norm_eq_abs] using hg1.norm
    calc
      _ ≤ D * (t : ℝ) ^ (-(d : ℝ) / 4) * ∫ x, |g x| := hdec t ht g hgvol hg2
      _ ≤ D * (t : ℝ) ^ (-(d : ℝ) / 4) * (K * ∫ x, |g x| ∂μ) :=
        mul_le_mul_of_nonneg_left hmass (mul_nonneg hD.le hpow)
      _ = _ := by ring

#print axioms u7_unforced_physical_L2_to_Linfty_decay

end EinsteinFull

namespace EinsteinFull

/-- Quantitative L¹-to-L∞ smoothing for the unforced physical semigroup. -/
theorem u7_unforced_physical_L1_to_Linfty_decay
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ)
    (hΛ : 1 ≤ Λ) (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t →
      ∀ (g : Vec d → ℝ) (_hg1 : Integrable g volume)
        (hg2 : MemLp g 2 (physicalReversibleMeasure ω hd 0)),
        ∀ᵐ x ∂physicalReversibleMeasure ω hd 0,
          |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (hg2.toLp g) x| ≤
            C * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) * ∫ y, |g y| := by
  obtain ⟨C, hC, hInf⟩ := u7_unforced_physical_L2_to_Linfty_decay hd ω Λ hΛ hω
  obtain ⟨D, hD, h₂⟩ := u7_unforced_physical_L1_to_L2 hd ω Λ hΛ hω
  refine ⟨C * D, mul_pos hC hD, ?_⟩
  intro t ht g hg1 hg2
  have hh : 0 < t / 2 := by positivity
  have hhR : (0 : ℝ) < ((t / 2 : ℝ≥0) : ℝ) := hh
  have hpow : 0 ≤ (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 4)) :=
    Real.rpow_nonneg hhR.le _
  have hbound := h₂ (t / 2) hh g hg1 hg2
  filter_upwards [hInf (t / 2) hh (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω
    (t / 2) (hg2.toLp g))] with x hx
  calc
    _ = |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω (t / 2)
        (Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω (t / 2) (hg2.toLp g)) x| := by
      rw [u8_physical_half_time]
    _ ≤ C * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 4)) *
        ‖Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω (t / 2) (hg2.toLp g)‖ := hx
    _ ≤ (C * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 4))) *
        (D * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 4)) * ∫ y, |g y|) :=
      mul_le_mul_of_nonneg_left hbound (mul_nonneg hC.le hpow)
    _ = _ := by
      have hp : -(d : ℝ) / 4 + -(d : ℝ) / 4 = -(d : ℝ) / 2 := by ring
      have hp2 : (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 4)) *
          (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 4)) =
          (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2)) := by
        rw [← Real.rpow_add hhR, hp]
      rw [← hp2]
      ring

#print axioms u7_unforced_physical_L1_to_Linfty_decay

end EinsteinFull

namespace EinsteinFull

/-- A quantitative every-start bound for the unforced physical kernel. -/
theorem u7_unforced_kernel_quantitative_domination {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t → ∀ x,
      u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x ≤
        ENNReal.ofReal (C * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2))) •
          (volume : Measure (Vec d)) := by
  obtain ⟨C, hC, hbound⟩ := u7_unforced_physical_L1_to_Linfty_decay hd ω Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro t ht
  have hh : (0 : ℝ) < ((t / 2 : ℝ≥0) : ℝ) := by positivity
  let M := C * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2))
  have hM : 0 ≤ M := mul_nonneg hC.le (Real.rpow_nonneg hh.le _)
  let P := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  apply u2_finite_kernel_domination_of_ae_compact_tests (P t) M hM
  · intro f
    change Continuous (fun x => ∫ y, f y ∂(u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x))
    simp_rw [u2RegularC0KernelSemigroup_integral]
    exact (u2RegularC0Semigroup hd ω 0 Λ hΛ hω t f).continuous
  · intro f hf hfc hfn
    have hf1 : Integrable f volume := hf.integrable_of_hasCompactSupport hfc
    have hf2 := Blueprint.gmpPhysical_compactContinuous_memLp hd ω 0 f hf hfc
    let g : ZeroAtInftyContinuousMap (Vec d) ℝ := ⟨⟨f, hf⟩, hfc.is_zero_at_infty⟩
    have hac : (volume : Measure (Vec d)) ≪ physicalReversibleMeasure ω hd 0 :=
      Measure.absolutelyContinuous_of_le_smul
        (u4_unforced_physical_measure_comparable hd ω Λ hω).2
    have he := u2RegularC0KernelSemigroup_integral_ae hd ω 0 Λ hΛ hω t g
      (hf2.toLp f) hf2.coeFn_toLp
    filter_upwards [hac.ae_eq he, hac.ae_le (hbound t ht f hf1 hf2)] with x he hb
    change (∫ y, f y ∂P t x) = _ at he
    rw [he]
    calc
      _ ≤ |Blueprint.gmpPhysicalSemigroup hd ω 0 Λ hΛ hω t (hf2.toLp f) x| := le_abs_self _
      _ ≤ M * ∫ y, |f y| := hb
      _ = M * ∫ y, f y := by simp only [abs_of_nonneg (hfn _)]

#print axioms u7_unforced_kernel_quantitative_domination

/-- A jointly measurable every-start density with quantitative Nash decay. -/
theorem u7_unforced_kernel_quantitative_density {d : ℕ}
    (hd : 2 ≤ d) (ω : FieldPair d) (Λ : ℝ) (hΛ : 1 ≤ Λ)
    (hω : IsRegular Λ ω) :
    ∃ C : ℝ, 0 < C ∧ ∀ (t : ℝ≥0), 0 < t →
      ∃ p : Vec d → Vec d → ℝ, Measurable (Function.uncurry p) ∧
        (∀ x y, 0 ≤ p x y ∧ p x y ≤
          C * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2))) ∧
        ∀ x, u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω t x =
          (volume : Measure (Vec d)).withDensity (fun y => ENNReal.ofReal (p x y)) := by
  obtain ⟨C, hC, hdom⟩ := u7_unforced_kernel_quantitative_domination hd ω Λ hΛ hω
  refine ⟨C, hC, ?_⟩
  intro t ht
  let M := C * (((t / 2 : ℝ≥0) : ℝ) ^ (-(d : ℝ) / 2))
  have hh : (0 : ℝ) < ((t / 2 : ℝ≥0) : ℝ) := by positivity
  have hM : 0 ≤ M := mul_nonneg hC.le (Real.rpow_nonneg hh.le _)
  let P := u2RegularC0KernelSemigroup hd ω 0 Λ hΛ hω
  let : IsFiniteKernel (P t) := (P.isSubMarkovKernel t).isFiniteKernel
  have hac : ∀ x, P t x ≪ (volume : Measure (Vec d)) :=
    fun x => Measure.absolutelyContinuous_of_le_smul (hdom t ht x)
  obtain ⟨p, hp, hn, hr⟩ := u2_kernel_measurable_real_density_of_absolutelyContinuous (P t) hac
  obtain ⟨q, hq, hqb, hqr⟩ := u2_real_density_bounded_of_domination (P t) p hp hn hr M hM (hdom t ht)
  exact ⟨q, hq, hqb, hqr⟩

#print axioms u7_unforced_kernel_quantitative_density

end EinsteinFull
