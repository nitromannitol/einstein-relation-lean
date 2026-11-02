import EinsteinFull.Calculus.SbxS4KilledSpectralR01
import EinsteinFull.Calculus.U5SelfAdjointSemigroupAnalytic
import EinsteinFull.Blueprint.G1.Proofs.SbxS9WeakEvolution

open MeasureTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support

/-- A zero-boundary physical graph has a whole-space weak gradient after
zero extension. Both value and gradient are the actual graph representatives. -/
theorem s4_zeroBoundary_representative_zero_extension
    {d : ℕ} (hd : 2 ≤ d) (lam : ℝ) (U : Set (Vec d))
    (u : physicalH1ZeroBoundary U hd lam) :
    HasWeakGradient Set.univ
      (U.indicator (physicalH1SpaceRepresentative hd lam u.1).value)
      (U.indicator (fun x => WithLp.ofLp
        ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))) := by
  let g := physicalH1SpaceRepresentative hd lam u.1
  have hv : g.value =ᵐ[volume] densityWeightedH1SpaceValue u.1 := by
    apply (ae_withDensity_iff_volume_of_continuous_pos
      (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
      (physicalForceWeight_pos hd lam) _).mp
    have he : g.value_memLp.toLp g.value = densityWeightedH1SpaceValue u.1 :=
      congrArg Prod.fst (physicalH1SpaceRepresentative_pair hd lam u.1)
    exact g.value_memLp.coeFn_toLp.symm.trans (Filter.EventuallyEq.of_eq (congrArg
      (fun f : Lp ℝ 2 (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) => (f : Vec d → ℝ)) he))
  have hg : g.weakGradient =ᵐ[volume] densityWeightedH1SpaceGradient u.1 := by
    apply (ae_withDensity_iff_volume_of_continuous_pos
      (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
      (physicalForceWeight_pos hd lam) _).mp
    have he : g.gradient_memLp.toLp g.weakGradient = densityWeightedH1SpaceGradient u.1 :=
      congrArg Prod.snd (physicalH1SpaceRepresentative_pair hd lam u.1)
    exact g.gradient_memLp.coeFn_toLp.symm.trans (Filter.EventuallyEq.of_eq (congrArg
      (fun f : Lp (EuclideanSpace ℝ (Fin d)) 2 (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) =>
        (f : Vec d → EuclideanSpace ℝ (Fin d))) he))
  apply Correctors.hasWeakGradient_congr_ae isOpen_univ g.distributionalGradient
  · rw [Measure.restrict_univ]
    filter_upwards [hv, physicalH1ZeroBoundary_value_zero_off U hd lam u.1 u.2] with x hx hz
    by_cases h : x ∈ U
    · simp only [Set.indicator_of_mem h]
      rfl
    · simp only [Set.indicator_of_notMem h, hx, hz h]
  · rw [Measure.restrict_univ]
    filter_upwards [hg, physicalH1ZeroBoundary_gradient_zero_off U hd lam u.1 u.2] with x hx hz
    by_cases h : x ∈ U
    · simp only [Set.indicator_of_mem h]
      rfl
    · simp only [Set.indicator_of_notMem h, hx, hz h]
      rfl

/-- Each killed orbit of generator-domain data has a zero-extension weak
spatial gradient and represents the actual killed L² evolution. -/
theorem s4_killed_orbit_zero_extension
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (z : (gmpKilledInteriorSemigroup r U hU).generatorDomain)
    (t : ℝ) (ht : 0 < t) :
    ∃ u : physicalH1ZeroBoundary U hd lam,
      physicalZeroBoundaryValue U hd ω lam L hω u =
        ((gmpKilledInteriorSemigroup r U hU t.toNNReal z).val) ∧
      HasWeakGradient Set.univ
        (U.indicator (physicalH1SpaceRepresentative hd lam u.1).value)
        (U.indicator (fun x => WithLp.ofLp
          ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))) := by
  obtain ⟨u, hu, _⟩ := s4_killed_orbit_weak_heat_equation r U hU z t ht
  exact ⟨u, hu, s4_zeroBoundary_representative_zero_extension hd lam U u⟩

/-- The actual killed expectation of generator-domain data has a global weak
spatial gradient, with zero Sobolev trace on the domain complement. -/
theorem s4_killed_expectation_zero_extension
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (z : (gmpKilledInteriorSemigroup r U hU).generatorDomain)
    (t : ℝ) (ht : 0 < t) :
    ∃ G : Vec d → Vec d,
      HasWeakGradient Set.univ
        (fun x => ∫ y, z.val.val y ∂gmpKilledEndpointKernel r U hU t.toNNReal x) G ∧
      ∀ x ∉ U, G x = 0 := by
  obtain ⟨u, hu, hw⟩ := s4_killed_orbit_zero_extension r U hU z t ht
  let g := physicalH1SpaceRepresentative hd lam u.1
  let G : Vec d → Vec d := U.indicator (fun x => WithLp.ofLp (g.weakGradient x))
  have hrep : g.value =ᵐ[volume] densityWeightedH1SpaceValue u.1 := by
    apply (ae_withDensity_iff_volume_of_continuous_pos
      (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
      (physicalForceWeight_pos hd lam) _).mp
    have he : g.value_memLp.toLp g.value = densityWeightedH1SpaceValue u.1 :=
      congrArg Prod.fst (physicalH1SpaceRepresentative_pair hd lam u.1)
    exact g.value_memLp.coeFn_toLp.symm.trans (Filter.EventuallyEq.of_eq (congrArg
      (fun f : Lp ℝ 2 (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) =>
        (f : Vec d → ℝ)) he))
  have hexpect : physicalZeroBoundaryValue U hd ω lam L hω u =ᵐ[volume]
      (fun x => ∫ y, z.val.val y ∂gmpKilledEndpointKernel r U hU t.toNNReal x) := by
    apply (ae_withDensity_iff_volume_of_continuous_pos
      (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
      (physicalReversibleDensity_pos ω hd lam) _).mp
    rw [hu]
    exact gmpKilledInteriorOperator_ae_eq r U hU t.toNNReal z.val
  have heq : U.indicator g.value =ᵐ[volume]
      (fun x => ∫ y, z.val.val y ∂gmpKilledEndpointKernel r U hU t.toNNReal x) := by
    filter_upwards [hrep, physicalZeroBoundaryValue_ae_eq_volume U hd ω lam L hω u,
      hexpect, physicalH1ZeroBoundary_value_zero_off U hd lam u.1 u.2] with x hx hy hz ho
    by_cases h : x ∈ U
    · rw [Set.indicator_of_mem h, hx, ← hy, hz]
    · rw [Set.indicator_of_notMem h, ← hz, hy, ho h]
  refine ⟨G, ?_, ?_⟩
  · apply Correctors.hasWeakGradient_congr_ae isOpen_univ hw
    · simpa only [Measure.restrict_univ] using heq
    · exact Filter.EventuallyEq.rfl
  · intro x hx
    exact Set.indicator_of_notMem hx _

/-- The literal killed expectation has the spatial and zero-extension weak
formulations on the open domain, using one common gradient. -/
theorem s4_killed_expectation_spatial_trace
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (z : (gmpKilledInteriorSemigroup r U hU).generatorDomain)
    (t : ℝ) (ht : 0 < t) :
    ∃ G : Vec d → Vec d,
      HasWeakGradient U
        (fun x => ∫ y, z.val.val y ∂gmpKilledEndpointKernel r U hU t.toNNReal x) G ∧
      HasWeakGradient Set.univ
        (U.indicator (fun x => ∫ y, z.val.val y ∂gmpKilledEndpointKernel r U hU t.toNNReal x))
        (U.indicator G) := by
  obtain ⟨G, hG, hzero⟩ := s4_killed_expectation_zero_extension r U hU z t ht
  refine ⟨G, Correctors.hasWeakGradient_mono (Set.subset_univ U) hG, ?_⟩
  have hf : U.indicator (fun x => ∫ y, z.val.val y ∂gmpKilledEndpointKernel r U hU t.toNNReal x) =
      (fun x => ∫ y, z.val.val y ∂gmpKilledEndpointKernel r U hU t.toNNReal x) := by
    funext x
    by_cases hx : x ∈ U
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx, gmpKilledEndpointKernel_eq_zero_of_notMem r U hU t.toNNReal x hx,
        integral_zero_measure]
  have hg : U.indicator G = G := by
    funext x
    by_cases hx : x ∈ U
    · exact Set.indicator_of_mem hx _
    · rw [Set.indicator_of_notMem hx, hzero x hx]
  rw [hf, hg]
  exact hG

/-- The physical L² pairing is the Lebesgue pairing with the actual mass
coefficient, valid for every real force. -/
theorem s4_physical_inner_lebesgue {d : ℕ} (hd : 2 ≤ d)
    (ω : FieldPair d) (lam : ℝ)
    (f g : Lp ℝ 2 (physicalReversibleMeasure ω hd lam)) :
    inner ℝ f g = ∫ x, s4PhysicalRho hd ω lam x * f x * g x := by
  rw [L2.inner_def, Work.W5.gantert_integral_physicalMeasure]
  apply integral_congr_ae
  filter_upwards with x
  simp only [RCLike.inner_apply, conj_trivial, s4PhysicalRho]
  ring


/-- The actual killed resolvent solves the physical weighted elliptic equation
for every interior L² datum and has zero Sobolev trace. -/
theorem s4_killed_resolvent_weighted_equation_and_trace
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (μ : MarkovProcess.Semigroup.PositiveShift)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    ∃ u : physicalH1ZeroBoundary U hd lam,
      physicalZeroBoundaryValue U hd ω lam L hω u =
        (gmpKilledInteriorResolvent r U hU μ f).val ∧
      HasWeakGradient Set.univ
        (U.indicator (physicalH1SpaceRepresentative hd lam u.1).value)
        (U.indicator (fun x => WithLp.ofLp
          ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))) ∧
      ∀ v : physicalH1ZeroBoundary U hd lam,
        (∫ x, dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
          ((s4PhysicalAlpha hd ω lam x).mulVec
            (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x)))) +
        (μ : ℝ) * (∫ x, s4PhysicalRho hd ω lam x *
          (gmpKilledInteriorResolvent r U hU μ f).val x *
          physicalZeroBoundaryValue U hd ω lam L hω v x) =
        ∫ x, s4PhysicalRho hd ω lam x * f.val x *
          physicalZeroBoundaryValue U hd ω lam L hω v x := by
  let S := gmpKilledInteriorSemigroup r U hU
  let z : S.generatorDomain := ⟨S.resolvent μ f, S.resolvent_mem_generatorDomain μ f⟩
  obtain ⟨u, hu, hform⟩ := s4_killed_generator_lebesgue_form r U hU z
  refine ⟨u, hu, s4_zeroBoundary_representative_zero_extension hd lam U u, ?_⟩
  intro v
  have h := hform v
  have hgen := S.generator_resolvent μ f
  change S.generator z = (μ : ℝ) • S.resolvent μ f - f at hgen
  have hgenval := congrArg Subtype.val hgen
  change (S.generator z).val = (μ : ℝ) • (gmpKilledInteriorResolvent r U hU μ f).val - f.val at hgenval
  rw [hgenval, inner_sub_left, real_inner_smul_left,
    s4_physical_inner_lebesgue, s4_physical_inner_lebesgue] at h
  linarith only [h]


/-- The actual killed orbit satisfies the separated weighted weak heat
identity together with the zero-extension trace of each spatial graph. -/
theorem s4_killed_orbit_weighted_integrated_equation_and_trace
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (z : (gmpKilledInteriorSemigroup r U hU).generatorDomain)
    (v : physicalH1ZeroBoundary U hd lam)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (η η' : ℝ → ℝ) (hη : ∀ t, HasDerivAt η (η' t) t)
    (hη' : Continuous η') (hηa : η a = 0) (hηb : η b = 0) :
    ∃ E : ℝ → ℝ, Continuous E ∧
      (∀ t : ℝ, ∃ u : physicalH1ZeroBoundary U hd lam,
        physicalZeroBoundaryValue U hd ω lam L hω u =
          ((gmpKilledInteriorSemigroup r U hU t.toNNReal z).val) ∧
        HasWeakGradient Set.univ
          (U.indicator (physicalH1SpaceRepresentative hd lam u.1).value)
          (U.indicator (fun x => WithLp.ofLp
            ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))) ∧
        E t = ∫ x, dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
          ((s4PhysicalAlpha hd ω lam x).mulVec
            (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x)))) ∧
      (∫ t in a..b, η' t * (∫ x, s4PhysicalRho hd ω lam x *
        (gmpKilledInteriorSemigroup r U hU t.toNNReal z).val x *
        physicalZeroBoundaryValue U hd ω lam L hω v x)) =
        ∫ t in a..b, η t * E t := by
  obtain ⟨E, hc, hE, heq⟩ := s4_killed_orbit_integrated_weak_equation
    r U hU z v a b ha hab η η' hη hη' hηa hηb
  refine ⟨E, hc, ?_, ?_⟩
  · intro t
    obtain ⟨u, hu, henergy⟩ := hE t
    exact ⟨u, hu, s4_zeroBoundary_representative_zero_extension hd lam U u, henergy⟩
  · convert heq using 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    congr 1
    change (∫ x, s4PhysicalRho hd ω lam x *
      (gmpKilledInteriorSemigroup r U hU t.toNNReal z).val x *
      physicalZeroBoundaryValue U hd ω lam L hω v x) =
      inner ℝ (gmpKilledInteriorSemigroup r U hU t.toNNReal z).val
        (physicalZeroBoundaryValue U hd ω lam L hω v)
    exact (s4_physical_inner_lebesgue hd ω lam _ _).symm


/-- Arbitrary interior L² data are approximated by generator-domain data
whose actual killed orbits have zero Sobolev trace. The approximation error
is controlled uniformly over all nonnegative times. -/
theorem s4_killed_orbit_approximation_with_zero_trace
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    ∃ z : ℕ → (gmpKilledInteriorSemigroup r U hU).generatorDomain,
      Tendsto (fun n => (z n).val) atTop (𝓝 f) ∧
      (∀ n t, dist (gmpKilledInteriorSemigroup r U hU t (z n))
        (gmpKilledInteriorSemigroup r U hU t f) ≤ dist (z n).val f) ∧
      ∀ n (t : ℝ), 0 < t → ∃ G : Vec d → Vec d,
        HasWeakGradient U
          (fun x => ∫ y, (z n).val.val y ∂gmpKilledEndpointKernel r U hU t.toNNReal x) G ∧
        HasWeakGradient Set.univ
          (U.indicator (fun x => ∫ y, (z n).val.val y ∂gmpKilledEndpointKernel r U hU t.toNNReal x))
          (U.indicator G) := by
  let S := gmpKilledInteriorSemigroup r U hU
  obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp (S.dense_generatorDomain f)
  refine ⟨fun n => ⟨u n, hu n⟩, hlim, ?_, ?_⟩
  · intro n t
    exact S.dist_apply_le t (u n) f
  · intro n t ht
    exact s4_killed_expectation_spatial_trace r U hU ⟨u n, hu n⟩ t ht


/-- The physical energy of the difference of two actual killed orbits is
bounded by the squared initial L² distance. -/
theorem s4_killed_orbit_difference_energy_bound
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (z w : (gmpKilledInteriorSemigroup r U hU).generatorDomain) :
    ∃ E : ℝ → ℝ, Continuous E ∧
      (∀ t : ℝ, ∃ u : physicalH1ZeroBoundary U hd lam,
        physicalZeroBoundaryValue U hd ω lam L hω u =
          (gmpKilledInteriorSemigroup r U hU t.toNNReal z).val -
          (gmpKilledInteriorSemigroup r U hU t.toNNReal w).val ∧
        HasWeakGradient Set.univ
          (U.indicator (physicalH1SpaceRepresentative hd lam u.1).value)
          (U.indicator (fun x => WithLp.ofLp
            ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))) ∧
        E t = ∫ x, dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
          ((s4PhysicalAlpha hd ω lam x).mulVec
            (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)))) ∧
      ∀ T : ℝ≥0, 2 * (∫ t in (0 : ℝ)..(T : ℝ), E t) ≤ ‖z.val - w.val‖ ^ 2 := by
  obtain ⟨E, hc, hE, hbalance⟩ := s4_killed_orbit_energy_identity r U hU (z - w)
  refine ⟨E, hc, ?_, ?_⟩
  · intro t
    obtain ⟨u, hu, henergy⟩ := hE t
    refine ⟨u, ?_, s4_zeroBoundary_representative_zero_extension hd lam U u, henergy⟩
    simpa only [Submodule.coe_sub, map_sub] using hu
  · intro T
    have h := hbalance T
    have hn : 0 ≤ ‖gmpKilledInteriorSemigroup r U hU T (z - w)‖ ^ 2 := sq_nonneg _
    simp only [Submodule.coe_sub] at h
    linarith only [h, hn]


/-- Ellipticity controls the physical L² gradient of every zero-boundary
spatial graph by its full anisotropic Lebesgue-normalized energy. -/
theorem s4_physical_gradient_le_anisotropic_energy
    {d : ℕ} (hd : 2 ≤ d) {L : ℝ} (hL : 1 ≤ L)
    {ω : FieldPair d} (hω : IsRegular L ω) (lam : ℝ)
    (U : Set (Vec d)) (u : physicalH1ZeroBoundary U hd lam) :
    (∫ x, ‖(physicalH1SpaceRepresentative hd lam u.1).weakGradient x‖ ^ 2
      ∂physicalReversibleMeasure ω hd lam) ≤
      2 * L * (∫ x, dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
        ((s4PhysicalAlpha hd ω lam x).mulVec
          (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)))) := by
  have h := SbxS9WeakEvolution.physical_gradient_energy_le hd hL (hω := hω)
    (physicalH1SpaceRepresentative hd lam u.1)
  unfold physicalH1FormEnergy at h
  rw [s4_physical_form_lebesgue] at h
  exact h


/-- Differences of actual killed orbits admit zero-boundary graphs whose
physical gradients are controlled pointwise in time by a continuous energy;
the integrated energy is bounded by the initial L² difference. -/
theorem s4_killed_orbit_difference_gradient_energy_control
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (z w : (gmpKilledInteriorSemigroup r U hU).generatorDomain) :
    ∃ E : ℝ → ℝ, Continuous E ∧
      (∀ t : ℝ, ∃ u : physicalH1ZeroBoundary U hd lam,
        physicalZeroBoundaryValue U hd ω lam L hω u =
          (gmpKilledInteriorSemigroup r U hU t.toNNReal z).val -
          (gmpKilledInteriorSemigroup r U hU t.toNNReal w).val ∧
        HasWeakGradient Set.univ
          (U.indicator (physicalH1SpaceRepresentative hd lam u.1).value)
          (U.indicator (fun x => WithLp.ofLp
            ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))) ∧
        (∫ x, ‖(physicalH1SpaceRepresentative hd lam u.1).weakGradient x‖ ^ 2
          ∂physicalReversibleMeasure ω hd lam) ≤ 2 * L * E t) ∧
      ∀ T : ℝ≥0, 2 * (∫ t in (0 : ℝ)..(T : ℝ), E t) ≤ ‖z.val - w.val‖ ^ 2 := by
  obtain ⟨E, hc, hE, hbound⟩ := s4_killed_orbit_difference_energy_bound r U hU z w
  refine ⟨E, hc, ?_, hbound⟩
  intro t
  obtain ⟨u, hu, htrace, henergy⟩ := hE t
  refine ⟨u, hu, htrace, ?_⟩
  rw [henergy]
  exact s4_physical_gradient_le_anisotropic_energy hd hL hω lam U u


/-- Positive-time images of arbitrary interior L² data belong to the
actual killed generator domain, by symmetry of the killed semigroup. -/
theorem s4_killed_positive_time_mem_generatorDomain
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    gmpKilledInteriorSemigroup r U hU t f ∈
      (gmpKilledInteriorSemigroup r U hU).generatorDomain := by
  apply u5_symmetric_semigroup_positive_time_mem_generatorDomain
    (gmpKilledInteriorSemigroup r U hU) ?_ t ht f
  intro s a b
  exact ((gmpKilledInteriorOperator_isSymmetric r U hU s) a b).symm

/-- Every positive-time killed orbit of arbitrary interior L² data has an
actual zero-boundary H¹ graph and whole-space zero-extension gradient. -/
theorem s4_killed_arbitrary_orbit_zero_extension
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω) :
    ∃ u : physicalH1ZeroBoundary U hd lam,
      physicalZeroBoundaryValue U hd ω lam L hω u =
        (gmpKilledInteriorSemigroup r U hU t f).val ∧
      HasWeakGradient Set.univ
        (U.indicator (physicalH1SpaceRepresentative hd lam u.1).value)
        (U.indicator (fun x => WithLp.ofLp
          ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))) := by
  let S := gmpKilledInteriorSemigroup r U hU
  let z : S.generatorDomain := ⟨S t f, s4_killed_positive_time_mem_generatorDomain r U hU t ht f⟩
  obtain ⟨u, hu, _⟩ := s4_killed_generator_lebesgue_form r U hU z
  exact ⟨u, hu, s4_zeroBoundary_representative_zero_extension hd lam U u⟩


/-- The literal actual killed expectation of arbitrary interior L² data has
a whole-space weak gradient vanishing off the domain at positive times. -/
theorem s4_killed_arbitrary_expectation_zero_extension
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω)
    (t : ℝ) (ht : 0 < t) :
    ∃ G : Vec d → Vec d,
      HasWeakGradient Set.univ
        (fun x => ∫ y, f.val y ∂gmpKilledEndpointKernel r U hU t.toNNReal x) G ∧
      ∀ x ∉ U, G x = 0 := by
  obtain ⟨u, hu, hw⟩ := s4_killed_arbitrary_orbit_zero_extension r U hU t.toNNReal (Real.toNNReal_pos.mpr ht) f
  let g := physicalH1SpaceRepresentative hd lam u.1
  let G : Vec d → Vec d := U.indicator (fun x => WithLp.ofLp (g.weakGradient x))
  have hrep : g.value =ᵐ[volume] densityWeightedH1SpaceValue u.1 := by
    apply (ae_withDensity_iff_volume_of_continuous_pos
      (physicalForceWeight hd lam) (physicalForceWeight_continuous hd lam)
      (physicalForceWeight_pos hd lam) _).mp
    have he : g.value_memLp.toLp g.value = densityWeightedH1SpaceValue u.1 :=
      congrArg Prod.fst (physicalH1SpaceRepresentative_pair hd lam u.1)
    exact g.value_memLp.coeFn_toLp.symm.trans (Filter.EventuallyEq.of_eq (congrArg
      (fun f : Lp ℝ 2 (EinsteinRelation.External.GantertSection7Support.physicalForceMeasure hd lam) =>
        (f : Vec d → ℝ)) he))
  have hexpect : physicalZeroBoundaryValue U hd ω lam L hω u =ᵐ[volume]
      (fun x => ∫ y, f.val y ∂gmpKilledEndpointKernel r U hU t.toNNReal x) := by
    apply (ae_withDensity_iff_volume_of_continuous_pos
      (physicalReversibleDensity ω hd lam) (physicalReversibleDensity_continuous ω hd lam)
      (physicalReversibleDensity_pos ω hd lam) _).mp
    rw [hu]
    exact gmpKilledInteriorOperator_ae_eq r U hU t.toNNReal f
  have heq : U.indicator g.value =ᵐ[volume]
      (fun x => ∫ y, f.val y ∂gmpKilledEndpointKernel r U hU t.toNNReal x) := by
    filter_upwards [hrep, physicalZeroBoundaryValue_ae_eq_volume U hd ω lam L hω u,
      hexpect, physicalH1ZeroBoundary_value_zero_off U hd lam u.1 u.2] with x hx hy hz ho
    by_cases h : x ∈ U
    · rw [Set.indicator_of_mem h, hx, ← hy, hz]
    · rw [Set.indicator_of_notMem h, ← hz, hy, ho h]
  refine ⟨G, ?_, ?_⟩
  · apply Correctors.hasWeakGradient_congr_ae isOpen_univ hw
    · simpa only [Measure.restrict_univ] using heq
    · exact Filter.EventuallyEq.rfl
  · intro x hx
    exact Set.indicator_of_notMem hx _


/-- At every positive time, the actual killed orbit of arbitrary interior L²
data satisfies the physical weak heat equation with zero Sobolev trace. -/
theorem s4_killed_arbitrary_orbit_weak_heat_equation_and_trace
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω)
    (t : ℝ) (ht : 0 < t) :
    ∃ u : physicalH1ZeroBoundary U hd lam,
      physicalZeroBoundaryValue U hd ω lam L hω u =
        (gmpKilledInteriorSemigroup r U hU t.toNNReal f).val ∧
      HasWeakGradient Set.univ
        (U.indicator (physicalH1SpaceRepresentative hd lam u.1).value)
        (U.indicator (fun x => WithLp.ofLp
          ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))) ∧
      ∀ v : physicalH1ZeroBoundary U hd lam,
        HasDerivAt
          (fun s : ℝ => inner ℝ (gmpKilledInteriorSemigroup r U hU s.toNNReal f)
            (physicalZeroBoundaryInteriorValue U hd ω lam L hω v))
          (-(∫ x, dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
            ((s4PhysicalAlpha hd ω lam x).mulVec
              (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x))))) t := by
  let S := gmpKilledInteriorSemigroup r U hU
  let a : ℝ := t / 2
  have ha : 0 < a := by dsimp [a]; linarith
  have hat : a < t := by dsimp [a]; linarith
  let z : S.generatorDomain := ⟨S a.toNNReal f,
    s4_killed_positive_time_mem_generatorDomain r U hU a.toNNReal (Real.toNNReal_pos.mpr ha) f⟩
  obtain ⟨u, hu, hweak⟩ := s4_killed_orbit_weak_heat_equation r U hU z (t - a) (by linarith)
  have heq : (fun s : ℝ => S s.toNNReal f) =ᶠ[𝓝 t]
      (fun s : ℝ => S (s - a).toNNReal z) := by
    filter_upwards [Ioi_mem_nhds hat] with s hs
    have hsum : (s - a).toNNReal + a.toNNReal = s.toNNReal := by
      rw [← Real.toNNReal_add (sub_nonneg.mpr hs.le) ha.le]
      congr 1
      ring
    change S s.toNNReal f = S (s - a).toNNReal (S a.toNNReal f)
    rw [← hsum, S.add_apply]
  have hvalue : S t.toNNReal f = S (t - a).toNNReal z := heq.self_of_nhds
  refine ⟨u, ?_, s4_zeroBoundary_representative_zero_extension hd lam U u, ?_⟩
  · rw [hvalue]
    exact hu
  · intro v
    have hderiv := (hweak v).scomp t ((hasDerivAt_id t).sub_const a)
    have heq' : (fun s : ℝ => inner ℝ (S s.toNNReal f)
        (physicalZeroBoundaryInteriorValue U hd ω lam L hω v)) =ᶠ[𝓝 t]
        (fun s : ℝ => inner ℝ (S (s - a).toNNReal z)
          (physicalZeroBoundaryInteriorValue U hd ω lam L hω v)) := by
      filter_upwards [heq] with s hs
      rw [hs]
    simpa only [Function.comp_def, id_eq, one_smul] using hderiv.congr_of_eventuallyEq heq'


/-- Separated time tests for arbitrary interior L² data, with the physical
weighted energy and the zero-extension trace at every positive test time. -/
theorem s4_killed_arbitrary_orbit_weighted_integrated_equation_and_trace
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (f : physicalZeroBoundaryL2 U hd ω lam L hω)
    (v : physicalH1ZeroBoundary U hd lam)
    (a b : ℝ) (ha : 0 < a) (hab : a ≤ b)
    (η η' : ℝ → ℝ) (hη : ∀ t, HasDerivAt η (η' t) t)
    (hη' : Continuous η') (hηa : η a = 0) (hηb : η b = 0) :
    ∃ E : ℝ → ℝ, Continuous E ∧
      (∀ t ∈ Set.Icc a b, ∃ u : physicalH1ZeroBoundary U hd lam,
        physicalZeroBoundaryValue U hd ω lam L hω u =
          (gmpKilledInteriorSemigroup r U hU t.toNNReal f).val ∧
        HasWeakGradient Set.univ
          (U.indicator (physicalH1SpaceRepresentative hd lam u.1).value)
          (U.indicator (fun x => WithLp.ofLp
            ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))) ∧
        E t = ∫ x, dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
          ((s4PhysicalAlpha hd ω lam x).mulVec
            (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x)))) ∧
      (∫ t in a..b, η' t * (∫ x, s4PhysicalRho hd ω lam x *
        (gmpKilledInteriorSemigroup r U hU t.toNNReal f).val x *
        physicalZeroBoundaryValue U hd ω lam L hω v x)) =
        ∫ t in a..b, η t * E t := by
  let S := gmpKilledInteriorSemigroup r U hU
  let c : ℝ := a / 2
  have hc : 0 < c := by dsimp [c]; linarith
  have hca : c < a := by dsimp [c]; linarith
  let z : S.generatorDomain := ⟨S c.toNNReal f,
    s4_killed_positive_time_mem_generatorDomain r U hU c.toNNReal (Real.toNNReal_pos.mpr hc) f⟩
  let V := physicalZeroBoundaryInteriorValue U hd ω lam L hω v
  let F : ℝ → ℝ := fun t => inner ℝ (S t.toNNReal f) V
  let E : ℝ → ℝ := fun t => -inner ℝ (S (t - c).toNNReal (S.generator z)) V
  have hcF : Continuous F := (S.continuous_operator_toNNReal f).inner continuous_const
  have hcE : Continuous E :=
    (((S.continuous_operator_toNNReal _).comp (continuous_id.sub continuous_const)).inner
      continuous_const).neg
  have hcη : Continuous η := continuous_iff_continuousAt.mpr fun t => (hη t).continuousAt
  have heq (t : ℝ) (ht : c < t) : S t.toNNReal f = S (t - c).toNNReal z := by
    have hsum : (t - c).toNNReal + c.toNNReal = t.toNNReal := by
      rw [← Real.toNNReal_add (sub_nonneg.mpr ht.le) hc.le]
      congr 1
      ring
    change S t.toNNReal f = S (t - c).toNNReal (S c.toNNReal f)
    rw [← hsum, S.add_apply]
  refine ⟨E, hcE, ?_, ?_⟩
  · intro t ht
    have hct : c < t := lt_of_lt_of_le hca ht.1
    let zt : S.generatorDomain := ⟨S (t - c).toNNReal z,
      S.operator_mem_generatorDomain z (t - c).toNNReal⟩
    obtain ⟨u, hu, he⟩ := s4_killed_generator_lebesgue_form r U hU zt
    refine ⟨u, ?_, s4_zeroBoundary_representative_zero_extension hd lam U u, ?_⟩
    · rw [heq t hct]
      exact hu
    · have hf := he v
      rw [S.generator_operator] at hf
      exact hf.symm
  · have hF (t : ℝ) (ht : c < t) : HasDerivAt F (-E t) t := by
      have hh := ((S.hasDerivAt_operator_toNNReal z (by linarith : 0 < t - c)).scomp t
        ((hasDerivAt_id t).sub_const c)).inner ℝ (hasDerivAt_const t V)
      have hevent : F =ᶠ[𝓝 t] (fun s : ℝ => inner ℝ (S (s - c).toNNReal z) V) := by
        filter_upwards [Ioi_mem_nhds ht] with s hs
        exact congrArg (fun q => inner ℝ q V) (heq s hs)
      simpa only [Function.comp_def, id_eq, one_smul, inner_zero_right, zero_add,
        E, neg_neg] using hh.congr_of_eventuallyEq hevent
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := η) (u' := η') (v := F) (v' := fun t => -E t)
      hcη.continuousOn hcF.continuousOn (fun t _ => hη t)
      (fun t ht => hF t (lt_of_lt_of_le hca (by simpa only [min_eq_left hab] using ht.1.le)))
      (hη'.intervalIntegrable a b) (hcE.neg.intervalIntegrable a b)
    simp only [hηa, hηb, zero_mul, sub_zero, zero_sub,
      mul_neg, intervalIntegral.integral_neg] at hparts
    have heqint : (∫ t in a..b, η' t * (∫ x, s4PhysicalRho hd ω lam x *
        (S t.toNNReal f).val x * physicalZeroBoundaryValue U hd ω lam L hω v x)) =
        ∫ t in a..b, η' t * F t := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp only
      congr 1
      exact (s4_physical_inner_lebesgue hd ω lam _ _).symm
    rw [heqint]
    linarith only [hparts]


/-- After any positive time shift, gradients of differences of actual killed
orbits satisfy an integrated energy bound controlled by the initial L² data. -/
theorem s4_killed_arbitrary_orbit_difference_gradient_energy_control
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (f g : physicalZeroBoundaryL2 U hd ω lam L hω)
    (a : ℝ≥0) (ha : 0 < a) :
    ∃ E : ℝ → ℝ, Continuous E ∧
      (∀ t : ℝ, ∃ u : physicalH1ZeroBoundary U hd lam,
        physicalZeroBoundaryValue U hd ω lam L hω u =
          (gmpKilledInteriorSemigroup r U hU (t.toNNReal + a) f).val -
          (gmpKilledInteriorSemigroup r U hU (t.toNNReal + a) g).val ∧
        HasWeakGradient Set.univ
          (U.indicator (physicalH1SpaceRepresentative hd lam u.1).value)
          (U.indicator (fun x => WithLp.ofLp
            ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))) ∧
        (∫ x, ‖(physicalH1SpaceRepresentative hd lam u.1).weakGradient x‖ ^ 2
          ∂physicalReversibleMeasure ω hd lam) ≤ 2 * L * E t) ∧
      ∀ T : ℝ≥0, 2 * (∫ t in (0 : ℝ)..(T : ℝ), E t) ≤ ‖f - g‖ ^ 2 := by
  let S := gmpKilledInteriorSemigroup r U hU
  let z : S.generatorDomain := ⟨S a f,
    s4_killed_positive_time_mem_generatorDomain r U hU a ha f⟩
  let w : S.generatorDomain := ⟨S a g,
    s4_killed_positive_time_mem_generatorDomain r U hU a ha g⟩
  obtain ⟨E, hcont, hE, hbound⟩ :=
    s4_killed_orbit_difference_gradient_energy_control r U hU z w
  refine ⟨E, hcont, ?_, ?_⟩
  · intro t
    obtain ⟨u, hu, htrace, hgrad⟩ := hE t
    refine ⟨u, ?_, htrace, hgrad⟩
    change physicalZeroBoundaryValue U hd ω lam L hω u =
      (S (t.toNNReal + a) f).val - (S (t.toNNReal + a) g).val
    rw [S.add_apply, S.add_apply]
    exact hu
  · intro T
    have hn : ‖z.val - w.val‖ ≤ ‖f - g‖ := by
      simpa only [dist_eq_norm] using S.dist_apply_le a f g
    have hs : ‖z.val - w.val‖ ^ 2 ≤ ‖f - g‖ ^ 2 :=
      (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).2 hn
    exact (hbound T).trans hs


/-- Each actual killed point-source row has an integrable reversible density;
its integral is exactly the survival mass and is at most one. -/
theorem s4_actual_killed_reversible_density_integrable
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (y : Vec d) (hy : y ∈ U) :
    ∃ k : ℝ → Vec d → ℝ,
      (∀ t > 0, Measurable (k t)) ∧
      (∀ t > 0, ∀ x, 0 ≤ k t x) ∧
      (∀ t : ℝ, ∀ x ∉ U, k t x = 0) ∧
      (∀ t : ℝ, 0 < t → gmpKilledEndpointKernel r U hU t.toNNReal y =
        (physicalReversibleMeasure ω hd lam).withDensity
          (fun x => ENNReal.ofReal (k t x))) ∧
      (∀ t > 0, Integrable (k t) (physicalReversibleMeasure ω hd lam) ∧
        ENNReal.ofReal (∫ x, k t x ∂physicalReversibleMeasure ω hd lam) =
          gmpKilledEndpointKernel r U hU t.toNNReal y Set.univ ∧
        (∫ x, k t x ∂physicalReversibleMeasure ω hd lam) ≤ 1) ∧
      ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
        Tendsto (fun t : ℝ => ∫ x in U, (s4PhysicalRho hd ω lam x * k t x) * ψ x)
          (𝓝[>] (0 : ℝ)) (𝓝 (ψ y)) := by
  obtain ⟨k, hm, hn, hz, hr, hinit⟩ :=
    s4_actual_killed_reversible_density r U hU y hy
  refine ⟨k, hm, hn, hz, hr, ?_, hinit⟩
  intro t ht
  let μ := physicalReversibleMeasure ω hd lam
  have hmass : (∫⁻ x, ENNReal.ofReal (k t x) ∂μ) =
      gmpKilledEndpointKernel r U hU t.toNNReal y Set.univ := by
    rw [hr t ht, withDensity_apply _ MeasurableSet.univ]
    simp [μ]
  have hle : (∫⁻ x, ENNReal.ofReal (k t x) ∂μ) ≤ 1 := by
    rw [hmass]
    exact gmpKilledEndpointKernel_mass_le_one r U hU t.toNNReal y
  have hi : Integrable (k t) μ := by
    refine ⟨(hm t ht).aestronglyMeasurable, ?_⟩
    apply (hasFiniteIntegral_iff_ofReal (ae_of_all _ (hn t ht))).2
    exact lt_of_le_of_lt hle ENNReal.one_lt_top
  have heq : ENNReal.ofReal (∫ x, k t x ∂μ) =
      gmpKilledEndpointKernel r U hU t.toNNReal y Set.univ := by
    rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (hn t ht)), hmass]
  refine ⟨hi, heq, ?_⟩
  have h := hle
  rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ (hn t ht))] at h
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity : (0 : ℝ) ≤ 1)).mp (by simpa using h)


end EinsteinFull
