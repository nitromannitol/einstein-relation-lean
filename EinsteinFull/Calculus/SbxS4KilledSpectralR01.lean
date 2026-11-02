import EinsteinFull.Blueprint.G1.Proofs.SbxS8StoppedLocality
import EinsteinFull.Work.W5.GantertWeightedFormDynkinProof
import EinsteinRelation.Regeneration.HalfSpaces
import EinsteinFull.Calculus.U2GMPHeatDensity

open MeasureTheory Filter
open scoped NNReal ENNReal Topology InnerProductSpace

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.SpatialDirichlet
open EinsteinRelation.External.GantertSection7Support

/-- The literal reversible mass density for the physical diffusion. -/
noncomputable def s4PhysicalRho {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) : Vec d → ℝ := physicalReversibleDensity ω hd lam

/-- The coefficient in the source's divergence equation. The factor one half
comes from the physical Dirichlet form. -/
noncomputable def s4PhysicalAlpha {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (x : Vec d) : Mat d :=
  ((1 / 2 : ℝ) * s4PhysicalRho hd ω lam x) • ω.1 x

/-- The physical mass and energy factors in Lebesgue normalization. -/
theorem s4_physical_form_lebesgue {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d)
    (lam : ℝ) (u v : PhysicalH1Space hd lam) :
    (∫ x, weightedFormIntegrand ω.1 (physicalH1SpaceRepresentative hd lam u)
      (physicalH1SpaceRepresentative hd lam v) x ∂physicalReversibleMeasure ω hd lam) =
    ∫ x, dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u).weakGradient x))
      ((s4PhysicalAlpha hd ω lam x).mulVec
        (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v).weakGradient x))) := by
  rw [Work.W5.gantert_integral_physicalMeasure]
  apply integral_congr_ae
  filter_upwards with x
  simp only [weightedFormIntegrand, s4PhysicalAlpha, dot, Matrix.mulVec, dotProduct, s4PhysicalRho,
    Matrix.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The actual killed generator obeys the physical zero-boundary variational
identity with the coefficients normalized against Lebesgue measure. -/
theorem s4_killed_generator_lebesgue_form
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (z : (gmpKilledInteriorSemigroup r U hU).generatorDomain) :
    ∃ u : physicalH1ZeroBoundary U hd lam,
      physicalZeroBoundaryValue U hd ω lam L hω u = z.val.val ∧
      ∀ v : physicalH1ZeroBoundary U hd lam,
        (∫ x, dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
          ((s4PhysicalAlpha hd ω lam x).mulVec
            (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x)))) =
          -inner ℝ ((gmpKilledInteriorSemigroup r U hU).generator z).val
            (physicalZeroBoundaryValue U hd ω lam L hω v) := by
  obtain ⟨u, hu, hform⟩ := Blueprint.sbxS8_gmp_killedGenerator_isPhysicalPair r U hU z
  refine ⟨u, hu, fun v => ?_⟩
  rw [← s4_physical_form_lebesgue hd ω lam u.1 v.1]
  exact hform v

/-- Any nonnegative Lebesgue density representing the actual killed rows has
initial delta on bounded continuous tests supported inside the domain. The only
conditional input is the row representation; no PDE regularity is assumed. -/
theorem s4_killed_density_initial_delta_of_row_representation
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (y : Vec d) (hy : y ∈ U)
    (K : ℝ → Vec d → ℝ)
    (hKmeas : ∀ t > 0, Measurable (K t))
    (hKnonneg : ∀ t > 0, ∀ x, 0 ≤ K t x)
    (hrow : ∀ t : ℝ, 0 < t → gmpKilledEndpointKernel r U hU t.toNNReal y =
      volume.withDensity (fun x => ENNReal.ofReal (K t x)))
    (ψ : Vec d → ℝ) (hψ : Continuous ψ) (B : ℝ) (hB : ∀ x, |ψ x| ≤ B)
    (hzero : ∀ x, x ∉ U → ψ x = 0) :
    Tendsto (fun t : ℝ => ∫ x in U, K t x * ψ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (ψ y)) := by
  have htime : Tendsto (fun t : ℝ => t.toNNReal) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ≥0)) := by
    simpa using (continuous_real_toNNReal.tendsto (0 : ℝ)).mono_left nhdsWithin_le_nhds
  have hlim := (tendsto_integral_gmpKilledEndpointKernel_at_zero r U hU y hy ψ hψ B hB).comp htime
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  have heq : (∫ x, ψ x ∂gmpKilledEndpointKernel r U hU t.toNNReal y) =
      ∫ x, K t x * ψ x := by
    rw [hrow t ht, integral_withDensity_eq_integral_toReal_smul
      (hKmeas t ht).ennreal_ofReal (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)]
    simp only [ENNReal.toReal_ofReal (hKnonneg t ht _), smul_eq_mul]
  change (∫ x, ψ x ∂gmpKilledEndpointKernel r U hU t.toNNReal y) = _
  rw [heq]
  symm
  apply setIntegral_eq_integral_of_ae_compl_eq_zero
  exact ae_of_all _ (fun x hx => by rw [hzero x hx, mul_zero])

/-- The initial-delta clause for every source spatial test follows from an
actual killed-row representation and does not require a PDE premise. -/
theorem s4_killed_density_spatial_test_initial_delta_of_row_representation
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (y : Vec d) (hy : y ∈ U)
    (K : ℝ → Vec d → ℝ)
    (hKmeas : ∀ t > 0, Measurable (K t))
    (hKnonneg : ∀ t > 0, ∀ x, 0 ≤ K t x)
    (hrow : ∀ t : ℝ, 0 < t → gmpKilledEndpointKernel r U hU t.toNNReal y =
      volume.withDensity (fun x => ENNReal.ofReal (K t x)))
    (ψ : Vec d → ℝ) (hψ : IsSpatialTest U ψ) :
    Tendsto (fun t : ℝ => ∫ x in U, K t x * ψ x)
      (𝓝[>] (0 : ℝ)) (𝓝 (ψ y)) := by
  obtain ⟨B, hB⟩ := hψ.1.continuous.norm.bddAbove_range_of_hasCompactSupport hψ.2.1.norm
  apply s4_killed_density_initial_delta_of_row_representation r U hU y hy K
    hKmeas hKnonneg hrow ψ hψ.1.continuous B
  · intro x
    simpa only [Real.norm_eq_abs] using hB (Set.mem_range_self x)
  · intro x hx
    exact (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hψ.2.2 ht))).self_of_nhds

/-- Every interior start has a real nonnegative density of its actual killed
endpoint law whose spatial-test trace converges to the starting point. -/
theorem s4_actual_killed_density_initial_delta
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (y : Vec d) (hy : y ∈ U) :
    ∃ K : ℝ → Vec d → ℝ,
      (∀ t > 0, Measurable (K t)) ∧
      (∀ t > 0, ∀ x, 0 ≤ K t x) ∧
      (∀ t : ℝ, 0 < t → gmpKilledEndpointKernel r U hU t.toNNReal y =
        volume.withDensity (fun x => ENNReal.ofReal (K t x))) ∧
      ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
        Tendsto (fun t : ℝ => ∫ x in U, K t x * ψ x)
          (𝓝[>] (0 : ℝ)) (𝓝 (ψ y)) := by
  let K : ℝ → Vec d → ℝ := fun t x =>
    ((gmpKilledEndpointKernel r U hU t.toNNReal y).rnDeriv volume x).toReal
  have hm : ∀ t > 0, Measurable (K t) := by
    intro t ht
    exact (Measure.measurable_rnDeriv _ _).ennreal_toReal
  have hn : ∀ t > 0, ∀ x, 0 ≤ K t x := by
    intro t ht x
    exact ENNReal.toReal_nonneg
  have hr : ∀ t : ℝ, 0 < t → gmpKilledEndpointKernel r U hU t.toNNReal y =
      volume.withDensity (fun x => ENNReal.ofReal (K t x)) := by
    intro t ht
    letI := isFiniteKernel_gmpKilledEndpointKernel r U hU t.toNNReal
    have hac := gmpKilledEndpointKernel_absolutelyContinuous_volume r U hU t.toNNReal
      (Real.toNNReal_pos.mpr ht) y
    rw [← Measure.withDensity_rnDeriv_eq _ _ hac]
    apply withDensity_congr_ae
    filter_upwards [Measure.rnDeriv_lt_top (gmpKilledEndpointKernel r U hU t.toNNReal y)
      (volume : Measure (Vec d))] with x hx
    exact (ENNReal.ofReal_toReal (ne_of_lt hx)).symm
  exact ⟨K, hm, hn, hr, fun ψ hψ =>
    s4_killed_density_spatial_test_initial_delta_of_row_representation r U hU y hy K hm hn hr ψ hψ⟩

/-- Positive-time killed evolution of generator-domain data satisfies the
physical weak heat equation against every zero-boundary H¹ test. -/
theorem s4_killed_orbit_weak_heat_equation
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
      ∀ v : physicalH1ZeroBoundary U hd lam,
        HasDerivAt
          (fun s : ℝ => inner ℝ (gmpKilledInteriorSemigroup r U hU s.toNNReal z)
            (physicalZeroBoundaryInteriorValue U hd ω lam L hω v))
          (-(∫ x, dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
            ((s4PhysicalAlpha hd ω lam x).mulVec
              (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x))))) t := by
  let S := gmpKilledInteriorSemigroup r U hU
  let zt : S.generatorDomain := ⟨S t.toNNReal z, S.operator_mem_generatorDomain z t.toNNReal⟩
  obtain ⟨u, hu, hform⟩ := s4_killed_generator_lebesgue_form r U hU zt
  refine ⟨u, hu, fun v => ?_⟩
  have hh := (S.hasDerivAt_operator_toNNReal z ht).inner ℝ
    (hasDerivAt_const t (physicalZeroBoundaryInteriorValue U hd ω lam L hω v))
  simp only [inner_zero_right, zero_add] at hh
  have he := hform v
  rw [S.generator_operator] at he
  convert hh using 1
  change -(∫ x, dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
    ((s4PhysicalAlpha hd ω lam x).mulVec
      (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x)))) =
    inner ℝ (S t.toNNReal (S.generator z)).val
      (physicalZeroBoundaryValue U hd ω lam L hω v)
  linarith only [he]

/-- The actual killed evolution has the physical energy dissipation identity;
its energy at each time is the Lebesgue-normalized zero-boundary form. -/
theorem s4_killed_orbit_energy_identity
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U)
    (z : (gmpKilledInteriorSemigroup r U hU).generatorDomain) :
    ∃ E : ℝ → ℝ, Continuous E ∧
      (∀ t : ℝ, ∃ u : physicalH1ZeroBoundary U hd lam,
        physicalZeroBoundaryValue U hd ω lam L hω u =
          ((gmpKilledInteriorSemigroup r U hU t.toNNReal z).val) ∧
        E t = ∫ x, dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
          ((s4PhysicalAlpha hd ω lam x).mulVec
            (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x)))) ∧
      ∀ T : ℝ≥0,
        ‖gmpKilledInteriorSemigroup r U hU T z‖ ^ 2 +
          2 * (∫ t in (0 : ℝ)..(T : ℝ), E t) = ‖z.val‖ ^ 2 := by
  let S := gmpKilledInteriorSemigroup r U hU
  let E : ℝ → ℝ := fun t => -inner ℝ (S t.toNNReal (S.generator z)) (S t.toNNReal z)
  have hc : Continuous E := by
    exact (((S.continuous_operator_toNNReal _).inner
      (S.continuous_operator_toNNReal _)).neg)
  refine ⟨E, hc, ?_, ?_⟩
  · intro t
    let zt : S.generatorDomain := ⟨S t.toNNReal z, S.operator_mem_generatorDomain z t.toNNReal⟩
    obtain ⟨u, hu, he⟩ := s4_killed_generator_lebesgue_form r U hU zt
    refine ⟨u, hu, ?_⟩
    have hf := he u
    rw [S.generator_operator, hu] at hf
    exact hf.symm
  · intro T
    have hderiv (t : ℝ) (ht : 0 < t) :
        HasDerivAt (fun s : ℝ => ‖S s.toNNReal z‖ ^ 2) (-2 * E t) t := by
      have h := S.hasDerivAt_operator_toNNReal z ht
      have hi := h.inner ℝ h
      simp only [real_inner_self_eq_norm_sq] at hi
      convert hi using 1
      dsimp [E]
      rw [real_inner_comm]
      ring
    have hcont : Continuous (fun t : ℝ => ‖S t.toNNReal z‖ ^ 2) :=
      (S.continuous_operator_toNNReal z).norm.pow 2
    have he := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le T.coe_nonneg
      hcont.continuousOn (fun t ht => hderiv t ht.1)
      ((hc.const_mul (-2)).intervalIntegrable 0 T)
    simp only [intervalIntegral.integral_const_mul, Real.toNNReal_coe,
      Real.toNNReal_zero, MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.zero_apply] at he
    linarith only [he]

/-- Separated time tests satisfy the integrated weak equation for actual killed
orbits, with the energy term represented by the physical zero-boundary form. -/
theorem s4_killed_orbit_integrated_weak_equation
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
        E t = ∫ x, dot (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam u.1).weakGradient x))
          ((s4PhysicalAlpha hd ω lam x).mulVec
            (WithLp.ofLp ((physicalH1SpaceRepresentative hd lam v.1).weakGradient x)))) ∧
      (∫ t in a..b, η' t * inner ℝ (gmpKilledInteriorSemigroup r U hU t.toNNReal z)
        (physicalZeroBoundaryInteriorValue U hd ω lam L hω v)) =
        ∫ t in a..b, η t * E t := by
  let S := gmpKilledInteriorSemigroup r U hU
  let V := physicalZeroBoundaryInteriorValue U hd ω lam L hω v
  let F : ℝ → ℝ := fun t => inner ℝ (S t.toNNReal z) V
  let E : ℝ → ℝ := fun t => -inner ℝ (S t.toNNReal (S.generator z)) V
  have hcF : Continuous F := (S.continuous_operator_toNNReal z).inner continuous_const
  have hcE : Continuous E := ((S.continuous_operator_toNNReal _).inner continuous_const).neg
  have hcη : Continuous η := continuous_iff_continuousAt.mpr fun t => (hη t).continuousAt
  refine ⟨E, hcE, ?_, ?_⟩
  · intro t
    let zt : S.generatorDomain := ⟨S t.toNNReal z, S.operator_mem_generatorDomain z t.toNNReal⟩
    obtain ⟨u, hu, he⟩ := s4_killed_generator_lebesgue_form r U hU zt
    refine ⟨u, hu, ?_⟩
    have hf := he v
    rw [S.generator_operator] at hf
    exact hf.symm
  · have hF (t : ℝ) (ht : 0 < t) : HasDerivAt F (-E t) t := by
      have hh := (S.hasDerivAt_operator_toNNReal z ht).inner ℝ (hasDerivAt_const t V)
      simpa only [inner_zero_right, zero_add, E, neg_neg] using hh
    have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
      (u := η) (u' := η') (v := F) (v' := fun t => -E t)
      hcη.continuousOn hcF.continuousOn (fun t _ => hη t)
      (fun t ht => hF t (lt_trans ha (by simpa only [min_eq_left hab] using ht.1)))
      (hη'.intervalIntegrable a b) (hcE.neg.intervalIntegrable a b)
    simp only [hηa, hηb, zero_mul, sub_zero, zero_sub,
      mul_neg, intervalIntegral.integral_neg] at hparts
    linarith only [hparts]

/-- The actual killed density can be chosen to vanish pointwise outside the
open domain, while retaining every row and its spatial-test initial trace. -/
theorem s4_actual_killed_density_supported_initial_delta
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (y : Vec d) (hy : y ∈ U) :
    ∃ K : ℝ → Vec d → ℝ,
      (∀ t > 0, Measurable (K t)) ∧
      (∀ t > 0, ∀ x, 0 ≤ K t x) ∧
      (∀ t : ℝ, ∀ x ∉ U, K t x = 0) ∧
      (∀ t : ℝ, 0 < t → gmpKilledEndpointKernel r U hU t.toNNReal y =
        volume.withDensity (fun x => ENNReal.ofReal (K t x))) ∧
      ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
        Tendsto (fun t : ℝ => ∫ x in U, K t x * ψ x)
          (𝓝[>] (0 : ℝ)) (𝓝 (ψ y)) := by
  classical
  obtain ⟨K, hm, hn, hr, _⟩ := s4_actual_killed_density_initial_delta r U hU y hy
  let K' : ℝ → Vec d → ℝ := fun t => U.indicator (K t)
  have hm' : ∀ t > 0, Measurable (K' t) := by
    intro t ht
    exact (hm t ht).indicator hU.measurableSet
  have hn' : ∀ t > 0, ∀ x, 0 ≤ K' t x := by
    intro t ht x
    by_cases hx : x ∈ U
    · simpa [K', hx] using hn t ht x
    · simp [K', hx]
  have hz : ∀ t : ℝ, ∀ x ∉ U, K' t x = 0 := by
    intro t x hx
    simp [K', hx]
  have hr' : ∀ t : ℝ, 0 < t → gmpKilledEndpointKernel r U hU t.toNNReal y =
      volume.withDensity (fun x => ENNReal.ofReal (K' t x)) := by
    intro t ht
    have hs := gmpKilledEndpointKernel_ae_mem r U hU t.toNNReal y
    rw [hr t ht, ae_withDensity_iff (hm t ht).ennreal_ofReal] at hs
    rw [hr t ht]
    apply withDensity_congr_ae
    filter_upwards [hs] with x hx
    by_cases hxu : x ∈ U
    · simp [K', hxu]
    · have hzero : ENNReal.ofReal (K t x) = 0 := by
        by_contra hne
        exact hxu (hx hne)
      simpa [K', hxu] using hzero
  exact ⟨K', hm', hn', hz, hr', fun ψ hψ =>
    s4_killed_density_spatial_test_initial_delta_of_row_representation r U hU y hy K'
      hm' hn' hr' ψ hψ⟩

/-- Converting a kernel symmetric with respect to reversible mass into the
Lebesgue density of an endpoint row introduces the ratio of mass densities. -/
theorem s4_reversible_kernel_density_transfer
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ)
    (y : Vec d) (k : Vec d → ℝ) (hk : Measurable k) :
    (physicalReversibleMeasure ω hd lam).withDensity
        (fun x => ENNReal.ofReal (k x)) =
      volume.withDensity (fun x => ENNReal.ofReal
        ((s4PhysicalRho hd ω lam x / s4PhysicalRho hd ω lam y) *
          (s4PhysicalRho hd ω lam y * k x))) := by
  have hr : Measurable (fun x => ENNReal.ofReal (s4PhysicalRho hd ω lam x)) := by
    exact (continuousSourcePhysicalDensity ω hd lam).measurable.ennreal_ofReal
  change (volume.withDensity (fun x => ENNReal.ofReal (s4PhysicalRho hd ω lam x))).withDensity _ = _
  rw [← withDensity_mul volume hr hk.ennreal_ofReal]
  apply congrArg (Measure.withDensity volume)
  funext x
  rw [Pi.mul_apply, ← ENNReal.ofReal_mul (show 0 ≤ s4PhysicalRho hd ω lam x from (physicalReversibleDensity_pos ω hd lam x).le)]
  congr 1
  have hy : s4PhysicalRho hd ω lam y ≠ 0 := (physicalReversibleDensity_pos ω hd lam y).ne'
  field_simp

/-- For zero potential, the signed-force ratio is exactly the exponential of
 the coordinate displacement. -/
theorem s4_zero_potential_density_ratio
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam : ℝ)
    (hV : ∀ x, ω.2 x = 0) (x y : Vec d) :
    s4PhysicalRho hd ω lam x / s4PhysicalRho hd ω lam y =
      Real.exp (2 * lam * ((x - y) (firstCoordinateIndex hd))) := by
  simp only [s4PhysicalRho, physicalReversibleDensity, physicalForceWeight, clockDensity, hV,
    mul_zero, neg_zero, Real.exp_zero, mul_one, ← Real.exp_sub, Pi.sub_apply]
  congr 1
  ring

/-- The structural lower bound is uniform in the environment and signed force
once the tube geometry has fixed the product of force and displacement. -/
theorem s4_zero_potential_density_ratio_lower
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam C l : ℝ)
    (hV : ∀ x, ω.2 x = 0) (x y : Vec d)
    (hgeom : |lam| * euclideanNorm (x - y) ≤ C * l) :
    Real.exp (-2 * C * l) ≤
      s4PhysicalRho hd ω lam x / s4PhysicalRho hd ω lam y := by
  rw [s4_zero_potential_density_ratio hd ω lam hV x y]
  apply Real.exp_le_exp.mpr
  have hc := Regeneration.coordinate_abs_le_euclideanNorm (x - y) (firstCoordinateIndex hd)
  have ha : |lam * ((x - y) (firstCoordinateIndex hd))| ≤ C * l := by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hc (abs_nonneg lam)).trans hgeom
  have hb := (abs_le.mp ha).1
  nlinarith

/-- A source lower bound transfers to an endpoint lower bound with a constant
chosen only from the tube geometry. -/
theorem s4_zero_potential_endpoint_lower_of_source_lower
    {d : ℕ} (hd : 2 ≤ d) (ω : FieldPair d) (lam C l : ℝ)
    (hV : ∀ x, ω.2 x = 0) (x y : Vec d)
    (hgeom : |lam| * euclideanNorm (x - y) ≤ C * l)
    (K c : ℝ) (hc : 0 ≤ c) (hK : c ≤ K) :
    Real.exp (-2 * C * l) * c ≤
      (s4PhysicalRho hd ω lam x / s4PhysicalRho hd ω lam y) * K := by
  exact mul_le_mul (s4_zero_potential_density_ratio_lower hd ω lam C l hV x y hgeom)
    hK hc (div_nonneg (physicalReversibleDensity_pos ω hd lam x).le
      (physicalReversibleDensity_pos ω hd lam y).le)

/-- Every interior start has a nonnegative reversible-measure density for its
actual killed endpoint row. This construction does not assert symmetry or
regularity in the starting point. -/
theorem s4_actual_killed_reversible_density
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
      ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
        Tendsto (fun t : ℝ => ∫ x in U, (s4PhysicalRho hd ω lam x * k t x) * ψ x)
          (𝓝[>] (0 : ℝ)) (𝓝 (ψ y)) := by
  obtain ⟨p, hpm, hpn, hpz, hpr, hpinit⟩ :=
    s4_actual_killed_density_supported_initial_delta r U hU y hy
  let k : ℝ → Vec d → ℝ := fun t x => p t x / s4PhysicalRho hd ω lam x
  have hrho : Continuous (s4PhysicalRho hd ω lam) :=
    continuousSourcePhysicalDensity ω hd lam
  have hpos : ∀ x, 0 < s4PhysicalRho hd ω lam x :=
    physicalReversibleDensity_pos ω hd lam
  have heq : ∀ t x, s4PhysicalRho hd ω lam x * k t x = p t x := by
    intro t x
    dsimp [k]
    field_simp [(hpos x).ne']
  have hkm : ∀ t > 0, Measurable (k t) := by
    intro t ht
    exact (hpm t ht).div hrho.measurable
  refine ⟨k, hkm, ?_, ?_, ?_, ?_⟩
  · intro t ht x
    exact div_nonneg (hpn t ht x) (hpos x).le
  · intro t x hx
    simp [k, hpz t x hx]
  · intro t ht
    rw [hpr t ht, s4_reversible_kernel_density_transfer hd ω lam y (k t) (hkm t ht)]
    apply congrArg (Measure.withDensity volume)
    funext x
    congr 1
    rw [show s4PhysicalRho hd ω lam x / s4PhysicalRho hd ω lam y *
      (s4PhysicalRho hd ω lam y * k t x) =
        s4PhysicalRho hd ω lam x * k t x by
          field_simp [(hpos y).ne']]
    exact (heq t x).symm
  · intro ψ hψ
    simpa only [heq] using hpinit ψ hψ

/-- At each positive time the actual killed rows have a jointly measurable
reversible-measure density, and their density integrals satisfy detailed balance.
This does not assert pointwise symmetry or continuity of the representative. -/
theorem s4_actual_killed_joint_reversible_density_balance
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t) :
    ∃ k : Vec d → Vec d → ℝ,
      Measurable (Function.uncurry k) ∧
      (∀ y x, 0 ≤ k y x) ∧
      (∀ y, gmpKilledEndpointKernel r U hU t y =
        (physicalReversibleMeasure ω hd lam).withDensity
          (fun x => ENNReal.ofReal (k y x))) ∧
      ∀ A B : Set (Vec d), MeasurableSet A → MeasurableSet B →
        (∫⁻ y in A, ∫⁻ x in B, ENNReal.ofReal (k y x)
          ∂physicalReversibleMeasure ω hd lam ∂physicalReversibleMeasure ω hd lam) =
        ∫⁻ x in B, ∫⁻ y in A, ENNReal.ofReal (k x y)
          ∂physicalReversibleMeasure ω hd lam ∂physicalReversibleMeasure ω hd lam := by
  letI := isFiniteKernel_gmpKilledEndpointKernel r U hU t
  obtain ⟨p, hp, hpn, hpr⟩ :=
    u2_kernel_measurable_real_density_of_absolutelyContinuous
      (gmpKilledEndpointKernel r U hU t)
      (gmpKilledEndpointKernel_absolutelyContinuous_volume r U hU t ht)
  let k : Vec d → Vec d → ℝ := fun y x => p y x / s4PhysicalRho hd ω lam x
  have hpos : ∀ x, 0 < s4PhysicalRho hd ω lam x :=
    physicalReversibleDensity_pos ω hd lam
  have hk : Measurable (Function.uncurry k) :=
    hp.div ((continuousSourcePhysicalDensity ω hd lam).measurable.comp measurable_snd)
  have hrow : ∀ y, gmpKilledEndpointKernel r U hU t y =
      (physicalReversibleMeasure ω hd lam).withDensity
        (fun x => ENNReal.ofReal (k y x)) := by
    intro y
    have hky : Measurable (k y) := hk.comp (measurable_const.prodMk measurable_id)
    rw [hpr y, s4_reversible_kernel_density_transfer hd ω lam y (k y) hky]
    apply congrArg (Measure.withDensity volume)
    funext x
    congr 1
    dsimp [k]
    field_simp [(hpos x).ne', (hpos y).ne']
  refine ⟨k, hk, fun y x => div_nonneg (hpn y x) (hpos x).le, hrow, ?_⟩
  intro A B hA hB
  have hb := gmpKilledEndpointKernel_physical_balance r U hU t A B hA hB
  simp_rw [hrow, withDensity_apply _ hA, withDensity_apply _ hB] at hb
  exact hb

/-- Source-normalized densities constructed from actual killed endpoint rows
have the Lebesgue initial delta, despite the reversible-weight conversion.
This establishes no positive-time spatial regularity or weak equation. -/
theorem s4_actual_source_normalized_density_initial_delta
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (y : Vec d) (hy : y ∈ U) :
    ∃ K : ℝ → Vec d → ℝ,
      (∀ t > 0, Measurable (K t)) ∧
      (∀ t > 0, ∀ x, 0 ≤ K t x) ∧
      (∀ t : ℝ, ∀ x ∉ U, K t x = 0) ∧
      (∀ t : ℝ, 0 < t → gmpKilledEndpointKernel r U hU t.toNNReal y =
        volume.withDensity (fun x => ENNReal.ofReal
          ((s4PhysicalRho hd ω lam x / s4PhysicalRho hd ω lam y) * K t x))) ∧
      ∀ ψ : Vec d → ℝ, IsSpatialTest U ψ →
        Tendsto (fun t : ℝ => ∫ x in U, K t x * ψ x)
          (𝓝[>] (0 : ℝ)) (𝓝 (ψ y)) := by
  obtain ⟨p, hpm, hpn, hpz, hpr, _⟩ :=
    s4_actual_killed_density_supported_initial_delta r U hU y hy
  let ρ := s4PhysicalRho hd ω lam
  have hc : Continuous ρ := continuousSourcePhysicalDensity ω hd lam
  have hpos : ∀ x, 0 < ρ x := physicalReversibleDensity_pos ω hd lam
  let K : ℝ → Vec d → ℝ := fun t x => (ρ y / ρ x) * p t x
  have hm : ∀ t > 0, Measurable (K t) := by
    intro t ht
    exact ((measurable_const.div hc.measurable).mul (hpm t ht))
  refine ⟨K, hm, ?_, ?_, ?_, ?_⟩
  · intro t ht x
    exact mul_nonneg (div_nonneg (hpos y).le (hpos x).le) (hpn t ht x)
  · intro t x hx
    simp [K, hpz t x hx]
  · intro t ht
    rw [hpr t ht]
    apply congrArg (Measure.withDensity volume)
    funext x
    congr 1
    change p t x = (ρ x / ρ y) * ((ρ y / ρ x) * p t x)
    field_simp [(hpos x).ne', (hpos y).ne']
  · intro ψ hψ
    let φ : Vec d → ℝ := fun x => (ρ y / ρ x) * ψ x
    have hφc : Continuous φ := (continuous_const.div hc (fun x => (hpos x).ne')).mul hψ.1.continuous
    have hφsupp : HasCompactSupport φ := hψ.2.1.mul_left
    obtain ⟨B, hB⟩ := hφc.norm.bddAbove_range_of_hasCompactSupport hφsupp.norm
    have hφzero : ∀ x, x ∉ U → φ x = 0 := by
      intro x hx
      have hψzero : ψ x = 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp (fun ht => hx (hψ.2.2 ht))).self_of_nhds
      simp [φ, hψzero]
    have hlim := s4_killed_density_initial_delta_of_row_representation r U hU y hy p
      hpm hpn hpr φ hφc B (fun x => by simpa only [Real.norm_eq_abs] using hB (Set.mem_range_self x)) hφzero
    have hφy : φ y = ψ y := by simp [φ, (hpos y).ne']
    rw [hφy] at hlim
    apply hlim.congr'
    filter_upwards with t
    apply setIntegral_congr_fun hU.measurableSet
    intro x hx
    dsimp [K, φ]
    ring


/-- On every finite reversible-measure region the jointly measurable density
of the actual killed transition is symmetric almost everywhere. -/
theorem s4_actual_killed_density_ae_symmetric_on_finite_region
    {d : ℕ} {hd : 2 ≤ d} {L : ℝ} {hL : 1 ≤ L}
    {ω : FieldPair d} {hω : IsRegular L ω}
    {lam : ℝ} {h0 : 0 ≤ lam} {h1 : lam ≤ 1}
    (r : GantertFixedEnvironmentRealization hd L hL ω hω lam h0 h1)
    (U : Set (Vec d)) (hU : IsOpen U) (t : ℝ≥0) (ht : 0 < t)
    (S : Set (Vec d)) (hS : MeasurableSet S)
    (hSf : physicalReversibleMeasure ω hd lam S ≠ ∞) :
    ∃ k : Vec d → Vec d → ℝ,
      Measurable (Function.uncurry k) ∧
      (∀ y x, 0 ≤ k y x) ∧
      (∀ y, gmpKilledEndpointKernel r U hU t y =
        (physicalReversibleMeasure ω hd lam).withDensity
          (fun x => ENNReal.ofReal (k y x))) ∧
      ∀ᵐ z ∂((physicalReversibleMeasure ω hd lam).restrict S).prod
          ((physicalReversibleMeasure ω hd lam).restrict S), k z.1 z.2 = k z.2 z.1 := by
  obtain ⟨k, hk, hn, hr, hb⟩ :=
    s4_actual_killed_joint_reversible_density_balance r U hU t ht
  let μ := physicalReversibleMeasure ω hd lam
  let ν := μ.restrict S
  letI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hSf
  let f : Vec d × Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal (k z.1 z.2)
  let g : Vec d × Vec d → ℝ≥0∞ := fun z => ENNReal.ofReal (k z.2 z.1)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp hk
  have hg : Measurable g := hf.comp measurable_swap
  have hfinite : ∫⁻ z, f z ∂ν.prod ν ≠ ∞ := by
    have hbound : ∫⁻ z, f z ∂ν.prod ν ≤ μ S := by
      rw [lintegral_prod f hf.aemeasurable]
      calc
        (∫⁻ y, ∫⁻ x, f (y, x) ∂ν ∂ν) ≤ ∫⁻ _y, (1 : ℝ≥0∞) ∂ν := by
          apply lintegral_mono
          intro y
          calc
            (∫⁻ x, f (y, x) ∂ν) ≤ ∫⁻ x, f (y, x) ∂μ := lintegral_mono' Measure.restrict_le_self le_rfl
            _ = gmpKilledEndpointKernel r U hU t y Set.univ := by
              rw [hr y, withDensity_apply _ MeasurableSet.univ]
              simp [f, μ]
            _ ≤ 1 := gmpKilledEndpointKernel_mass_le_one r U hU t y
        _ = μ S := by simp [ν, μ]
    exact ne_of_lt (lt_of_le_of_lt hbound (lt_top_iff_ne_top.mpr hSf))
  have hrect : ∀ ⦃A : Set (Vec d)⦄ (_ : MeasurableSet A)
      ⦃B : Set (Vec d)⦄ (_ : MeasurableSet B),
      ∫⁻ z in A ×ˢ B, f z ∂ν.prod ν = ∫⁻ z in A ×ˢ B, g z ∂ν.prod ν := by
    intro A hA B hB
    rw [setLIntegral_prod f hf.aemeasurable, setLIntegral_prod_symm g hg.aemeasurable]
    simpa [ν, Measure.restrict_restrict, hA, hB, Set.inter_comm] using
      hb (A ∩ S) (B ∩ S) (hA.inter hS) (hB.inter hS)
  have hae := ae_eq_of_setLIntegral_prod_eq hf.aemeasurable hg.aemeasurable hfinite hrect
  refine ⟨k, hk, hn, hr, ?_⟩
  filter_upwards [hae] with z hz
  have := congrArg ENNReal.toReal hz
  simpa [f, g, ENNReal.toReal_ofReal (hn _ _)] using this

end EinsteinFull
