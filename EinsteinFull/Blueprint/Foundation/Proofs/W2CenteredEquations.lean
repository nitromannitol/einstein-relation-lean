import EinsteinFull.Blueprint.Foundation.node_e_u3A_centered_u2D_equations
import EinsteinFull.Calculus.ComplexForcedGradientSupport
import EinsteinFull.Calculus.ComplexGeneratorSpatialSupport
import EinsteinFull.Blueprint.G3.Proofs.W3Queue0400_1
import EinsteinFull.Calculus.ComplexTransposeSpatialSupport
import EinsteinFull.Calculus.ComplexOperatorAnalyticSupport
import EinsteinFull.Work.W6.HorizontalPhysicalRealizationProof

open MeasureTheory Set Filter
open scoped NNReal ENNReal BigOperators Topology

noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

private instance reducedProbability {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- The actual drift observation has zero reduced-law mean. -/
theorem centeredEquations_drift_mean_zero {d : ℕ} {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (j : Fin d) : (∫ ω, β j ω ∂reducedLaw Q) = 0 := by
  have he := hβ.integral_mul j (Lp.const 2 (reducedLaw Q) 1) (fun _ => 0)
    (hasComplexHorizontalGradient_const _ (reducedLaw_stationary Q) 1)
  have hl : (∫ ω, β j ω * Lp.const 2 (reducedLaw Q) (1 : ℂ) ω ∂reducedLaw Q) =
      ∫ ω, β j ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
    simp only [hω, Function.const_apply, mul_one]
  have hr : (∫ ω, ∑ k : Fin d, (ω.1 0 k j : ℂ) *
      (0 : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp only [hω, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
  simpa only [hl, hr, mul_zero] using he

/-- Every actual indexed endpoint is centered, including the conservative
transpose, at every nonnegative time and signed complex force. -/
theorem centeredEquations_endpoint_mean_zero {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange} {hQ : HasSmoothBounds D Q}
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    {ζ : ℂ} {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d) (t : ℝ≥0) :
    (∫ ω, indexedEndpoint hd Q ν ζ P Pdag β a μ t ω ∂reducedLaw Q) = 0 := by
  rcases ν with j | b
  · exact integral_centeredComplexLp Q _
  · cases b
    · change (∫ ω, (ζ • centeredComplexLp Q (P t μ)) ω ∂reducedLaw Q) = 0
      rw [integral_congr_ae (Lp.coeFn_smul ζ _)]
      simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul,
        integral_centeredComplexLp, mul_zero]
    · change (∫ ω, Pdag t (β ⟨0, by omega⟩) ω ∂reducedLaw Q) = 0
      rw [hPdag.integral_eq hP, centeredEquations_drift_mean_zero hβ]

private theorem forward_weakFlux {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (hν : ν ≠ Sum.inr true)
    (ζ : ℂ) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a) (U : Lp ℂ 2 (reducedLaw Q))
    (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) U G) :
    ∃ J, IsEndpointWeakFlux hd Q ν ζ a U G J := by
  let F : Fin d → FieldPair d → ℂ := fun j ω =>
    ∑ k, ((ω.1 0 j k : ℂ) - (homogenizedCoefficient Q j k : ℂ)) * G k ω
  have hF (j : Fin d) : MemLp (F j) 2 (reducedLaw Q) := by
    apply memLp_finset_sum
    intro k _
    have hm := (Lp.memLp (complexCoefficientMul Q j k (G k))).ae_eq
      (complexCoefficientMul_coe Q j k (G k))
    simpa only [sub_mul, Pi.sub_apply] using!
      hm.sub ((Lp.memLp (G k)).const_mul (homogenizedCoefficient Q j k : ℂ))
  refine ⟨fun j => (hF j).toLp _, hG, ?_⟩
  intro j
  filter_upwards [(hF j).coeFn_toLp, ae_all_iff.mpr (fun k => ha j k)] with ω hω haω
  rw [hω]
  apply Finset.sum_congr rfl
  intro k _
  rcases ν with i | b
  · simp only [haω k, sub_zero]
  · cases b
    · simp only [haω k, sub_zero]
    · exact (hν rfl).elim

/-- Every positive-time forward velocity endpoint has the literal L2 weak flux.
Its coefficient products and the full anisotropic subtraction are constructed. -/
theorem centeredEquations_velocity_weakFlux {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a) {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (j : Fin d) (t : ℝ≥0) (ht : 0 < t) :
    ∃ G J, IsEndpointWeakFlux hd Q (.inl j) ζ a
      (velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a t) G J := by
  have hG := (hP.forcedGradient_spec t ht (β j + ζ • a ⟨0, by omega⟩ j)).centered
  obtain ⟨J, hJ⟩ := forward_weakFlux hd Q (.inl j) (by simp) ζ a ha _ _ hG
  exact ⟨_, J, hJ⟩

/-- The clock endpoint has its actual gradient and anisotropic weak flux at
positive time, including zero force. -/
theorem centeredEquations_clock_weakFlux {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
    (ha : IsReducedCoefficientObservation Q a) (μ : Lp ℂ 2 (reducedLaw Q)) {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ G J, IsEndpointWeakFlux hd Q (.inr false) ζ a (clockEndpoint Q ζ P μ t) G J := by
  have hG := (hP.forcedGradient_spec t ht μ).centered
  have hs : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (clockEndpoint Q ζ P μ t) (fun j => ζ • hP.forcedGradient t ht μ j) :=
    fun j => (hG j).smul ζ
  obtain ⟨J, hJ⟩ := forward_weakFlux hd Q (.inr false) (by simp) ζ a ha _ _ hs
  exact ⟨_, J, hJ⟩

/-- The full-domain forward orbit has a two-sided derivative at every positive
 time. The vector fundamental theorem of calculus supplies the left derivative. -/
theorem centeredEquations_forward_hasDerivAt {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    HasDerivAt (fun s : ℝ => P s.toNNReal f) (P t g) (t : ℝ) := by
  have hc : Continuous (fun s : ℝ => P s.toNNReal g) :=
    (hP.2.2.1 g).comp continuous_real_toNNReal
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const f
  simp only [Real.toNNReal_coe] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have he := hP.integral_generator_orbit hfg s.toNNReal
  rw [Real.coe_toNNReal s hs.le, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hs.le] at he
  exact (eq_sub_iff_add_eq.mp he).symm

/-- The true transpose orbit also has its actual two-sided time derivative at
 every positive time, obtained from its full generator-domain transport. -/
theorem centeredEquations_transpose_hasDerivAt {d : ℕ} {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexTransposeGeneratorPair Q i ζ f g)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    HasDerivAt (fun s : ℝ => T s.toNNReal f) (T t g) (t : ℝ) := by
  have hc : Continuous (fun s : ℝ => T s.toNNReal g) :=
    (hT.continuous_apply hP g).comp continuous_real_toNNReal
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 t)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const f
  simp only [Real.toNNReal_coe] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  have he := hT.integral_orbit_eq_sub hP hfg s.toNNReal
  rw [Real.coe_toNNReal s hs.le] at he
  exact (eq_sub_iff_add_eq.mp he).symm

/-- The actual centered velocity endpoint has a strong time derivative at
 every positive time; no generator-domain premise is imposed on its datum. -/
theorem centeredEquations_velocity_hasDerivAt {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    {ζ : ℂ} {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (j : Fin d) (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ∃ V, HasDerivAt (fun s : ℝ => velocityEndpoint Q ⟨0, by omega⟩ j ζ P β a
      s.toNNReal) V (t : ℝ) := by
  obtain ⟨g, hg⟩ := timeFlux_forward_initial_generator hβ ha j
  have he := ((centeredComplexLpCLM Q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (t : ℝ) (centeredEquations_forward_hasDerivAt hP hg t ht)
  change HasDerivAt (fun s : ℝ => centeredComplexLpCLM Q
    (P s.toNNReal (β j + ζ • a ⟨0, by omega⟩ j)))
    (centeredComplexLpCLM Q (P t g)) (t : ℝ) at he
  exact ⟨_, by simpa only [centeredComplexLpCLM_apply, velocityEndpoint] using he⟩

/-- The actual transpose endpoint simultaneously has its true conservative
 generator, strong time derivative and literal anisotropic L2 weak flux at
 every positive time. -/
theorem centeredEquations_transpose_domain_flux {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    {ζ : ℂ} {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    ∃ G J V,
      IsEndpointWeakFlux hd Q (.inr true) ζ a (transposeEndpoint Q ⟨0, by omega⟩ T β t) G J ∧
      IsComplexTransposeGeneratorPair Q ⟨0, by omega⟩ ζ
        (transposeEndpoint Q ⟨0, by omega⟩ T β t) V ∧
      HasDerivAt (fun s : ℝ => transposeEndpoint Q ⟨0, by omega⟩ T β s.toNNReal)
        V (t : ℝ) := by
  classical
  obtain ⟨g, hg⟩ := timeFlux_transpose_initial_generator (i := ⟨0, by omega⟩)
    (ζ := ζ) hβ ⟨0, by omega⟩
  have hgraph := hT.map_generator hP hg t
  obtain ⟨G, hG, _⟩ := hT.map_generator hP hg t
  let U := T t (β ⟨0, by omega⟩)
  let H : Fin d → Lp ℂ 2 (reducedLaw Q) := fun k =>
    G k - (2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) k : ℂ)) • U
  have hH (k : Fin d) : (H k : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => G k ω - 2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) k : ℂ) * U ω := by
    filter_upwards [Lp.coeFn_sub (G k) ((2 * ζ *
      (unitVector (⟨0, by omega⟩ : Fin d) k : ℂ)) • U),
      Lp.coeFn_smul (2 * ζ * (unitVector (⟨0, by omega⟩ : Fin d) k : ℂ)) U]
      with ω h1 h2
    simp only [H, h1, Pi.sub_apply, h2, Pi.smul_apply, smul_eq_mul]
  let F : Fin d → FieldPair d → ℂ := fun j ω =>
    ∑ k, ((ω.1 0 j k : ℂ) - (homogenizedCoefficient Q j k : ℂ)) * H k ω
  have hF (j : Fin d) : MemLp (F j) 2 (reducedLaw Q) := by
    apply memLp_finset_sum
    intro k _
    have hm := (Lp.memLp (complexCoefficientMul Q j k (H k))).ae_eq
      (complexCoefficientMul_coe Q j k (H k))
    simpa only [sub_mul, Pi.sub_apply] using!
      hm.sub ((Lp.memLp (H k)).const_mul (homogenizedCoefficient Q j k : ℂ))
  refine ⟨G, fun j => (hF j).toLp _, T t g, ⟨hG, ?_⟩, hgraph,
    centeredEquations_transpose_hasDerivAt hP hT hg t ht⟩
  intro j
  filter_upwards [(hF j).coeFn_toLp, ae_all_iff.mpr (fun k => ha j k),
    ae_all_iff.mpr hH] with ω hω haω hHω
  simp only [hω, F, haω, hHω]
  rfl

/-- The conservative transpose has the displayed centered equation on one
 environment event before all compact spatial tests. This is the complete
 transpose branch of the reviewed centered-equations contract. -/
theorem centeredEquations_transpose {d : ℕ} (hd : 2 ≤ d)
    {D : StructuralData d} {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q} {β : Fin d → Lp ℂ 2 (reducedLaw Q)}
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    {ζ : ℂ} {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    let U := transposeEndpoint Q ⟨0, by omega⟩ T β t
    ∃ (G J : Fin d → Lp ℂ 2 (reducedLaw Q)) (V : Lp ℂ 2 (reducedLaw Q)),
      IsEndpointWeakFlux hd Q (.inr true) ζ a U G J ∧
      HasDerivAt (fun s : ℝ => transposeEndpoint Q ⟨0, by omega⟩ T β s.toNNReal)
        V (t : ℝ) ∧
      (∫ ω, U ω ∂reducedLaw Q) = 0 ∧
      ∀ᵐ ω ∂reducedLaw Q,
        ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, V (translate x ω) * (φ x : ℂ)) +
            (1 / 2 : ℂ) * (∫ x, ∑ j : Fin d, ∑ k : Fin d,
              (homogenizedCoefficient Q j k : ℂ) * G k (translate x ω) *
                (coordinateDerivative j φ x : ℂ)) +
            ζ * (∫ x, (∑ j : Fin d,
              (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) *
                G j (translate x ω)) * (φ x : ℂ)) =
          -(1 / 2 : ℂ) * (∫ x, ∑ j : Fin d,
            J j (translate x ω) * (coordinateDerivative j φ x : ℂ)) := by
  classical
  letI : Fact (2 ≤ d) := ⟨hd⟩
  dsimp only
  obtain ⟨G, J, V, hJ, hgen, hder⟩ := centeredEquations_transpose_domain_flux hd hβ ha hP hT t ht
  let U := transposeEndpoint Q ⟨0, by omega⟩ T β t
  let A := homogenizedCoefficient Q
  let i : Fin d := ⟨0, by omega⟩
  have hraw (j : Fin d) : (J j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
      (∑ k, ((ω.1 0 j k : ℂ) - (A j k : ℂ)) * G k ω) -
        2 * ζ * ((ω.1 0 j i : ℂ) - (A j i : ℂ)) * U ω := by
    filter_upwards [hJ.2 j, ae_all_iff.mpr (fun k => ha j k)] with ω hj haω
    rw [hj]
    simp only [haω]
    change (∑ k, ((ω.1 0 j k : ℂ) - (A j k : ℂ)) *
      (G k ω - 2 * ζ * (unitVector i k : ℂ) * U ω)) = _
    have hp (k : Fin d) : ((ω.1 0 j k : ℂ) - (A j k : ℂ)) *
        (G k ω - 2 * ζ * (unitVector i k : ℂ) * U ω) =
        ((ω.1 0 j k : ℂ) - (A j k : ℂ)) * G k ω -
        (2 * ζ * U ω) * (((ω.1 0 j k : ℂ) - (A j k : ℂ)) *
          (unitVector i k : ℂ)) := by ring
    simp_rw [hp]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [unitVector, Pi.single_apply, apply_ite, Complex.ofReal_one,
      Complex.ofReal_zero, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true]
    ring
  have hsp (j : Fin d) := ae_complex_spatial_orbit_congr (reducedLaw Q)
    (reducedLaw_stationary Q) (Lp.stronglyMeasurable (J j)).measurable
    (by fun_prop) (hraw j)
  refine ⟨G, J, V, hJ, hder, ?_, ?_⟩
  · change (∫ ω, T t (β i) ω ∂reducedLaw Q) = 0
    rw [hT.integral_eq hP, centeredEquations_drift_mean_zero hβ]
  filter_upwards [hgen.spatial_flux_all_tests hJ.1, ae_all_iff.mpr hsp,
    hJ.1.ae_spatial_test,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) U,
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (G j)),
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (J j))] with ω he hr hib hU hG hJl
  intro φ hφ hφc
  have he := he φ hφ hφc
  have htest : IsSpatialTest Set.univ φ := ⟨hφ, hφc, Set.subset_univ _⟩
  have hdc (j : Fin d) : Continuous (coordinateDerivative j φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hUtest (j : Fin d) := integrable_spatial_mul_test hU (hdc j)
    (hφc.fderiv_apply ℝ (unitVector j))
  have hGtest (j k : Fin d) := integrable_spatial_mul_test (hG k) (hdc j)
    (hφc.fderiv_apply ℝ (unitVector j))
  have hJtest (j : Fin d) := integrable_spatial_mul_test (hJl j) (hdc j)
    (hφc.fderiv_apply ℝ (unitVector j))
  have hGj (j : Fin d) := integrable_spatial_mul_test (hG j) hφ.continuous hφc
  let B : Vec d → ℂ := fun x => ∑ j : Fin d, ∑ k : Fin d,
    (A j k : ℂ) * G k (translate x ω) * (coordinateDerivative j φ x : ℂ)
  let C : Vec d → ℂ := fun x => ∑ j : Fin d,
    (A j i : ℂ) * U (translate x ω) * (coordinateDerivative j φ x : ℂ)
  let F : Vec d → ℂ := fun x => ∑ j : Fin d,
    J j (translate x ω) * (coordinateDerivative j φ x : ℂ)
  have hB : Integrable B := integrable_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun k _ => by
      simpa only [mul_assoc] using (hGtest j k).const_mul (A j k : ℂ)
  have hC : Integrable C := integrable_finset_sum _ fun j _ => by
    simpa only [mul_assoc] using (hUtest j).const_mul (A j i : ℂ)
  have hF : Integrable F := integrable_finset_sum _ fun j _ => hJtest j
  have hsplit : (∫ x, ∑ j : Fin d,
      ((∑ k : Fin d, (ω.1 x j k : ℂ) * G k (translate x ω)) -
        2 * ζ * (ω.1 x j i : ℂ) * U (translate x ω)) *
          (coordinateDerivative j φ x : ℂ)) =
      (∫ x, F x) + (∫ x, B x) - (2 * ζ) * (∫ x, C x) := by
    suffices hh : (∫ x, ∑ j : Fin d,
        ((∑ k : Fin d, (ω.1 x j k : ℂ) * G k (translate x ω)) -
          2 * ζ * (ω.1 x j i : ℂ) * U (translate x ω)) *
            (coordinateDerivative j φ x : ℂ)) =
        ∫ x, (F x + B x) - (2 * ζ) * C x by
      have hFB : Integrable (fun x => F x + B x) := hF.add hB
      rw [hh, integral_sub hFB (hC.const_mul (2 * ζ)),
        integral_add hF hB, integral_const_mul]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hr] with x hx
    simp only [translate_matrix, add_zero] at hx
    dsimp only [F, B, C]
    simp only [← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hx j]
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    ring
  have hCeq : (∫ x, C x) = -(∫ x, (∑ j : Fin d,
      (A j i : ℂ) * G j (translate x ω)) * (φ x : ℂ)) := by
    rw [integral_finset_sum _ (fun j _ => by
      simpa only [mul_assoc] using (hUtest j).const_mul (A j i : ℂ))]
    have hib' (j : Fin d) : (∫ x, U (translate x ω) *
        (coordinateDerivative j φ x : ℂ)) =
        -(∫ x, G j (translate x ω) * (φ x : ℂ)) := hib j φ htest
    simp only [mul_assoc, integral_const_mul, hib', mul_neg,
      Finset.sum_neg_distrib]
    simp_rw [Finset.sum_mul]
    rw [integral_finset_sum _ (fun j _ => by
      simpa only [mul_assoc] using (hGj j).const_mul (A j i : ℂ))]
    simp only [mul_assoc, integral_const_mul]
  change (∫ x, V (translate x ω) * (φ x : ℂ)) = _ at he
  rw [hsplit, hCeq] at he
  change (∫ x, V (translate x ω) * (φ x : ℂ)) + (1 / 2 : ℂ) * (∫ x, B x) +
    ζ * (∫ x, (∑ j : Fin d, (A j i : ℂ) * G j (translate x ω)) * (φ x : ℂ)) =
      -(1 / 2 : ℂ) * (∫ x, F x)
  linear_combination he


variable {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}

private def centeredClockDirections : (cs : List (Fin d)) → Fin cs.length → Vec d
  | [] => Fin.elim0
  | k :: cs => Fin.cons (unitVector k) (centeredClockDirections cs)

private theorem centeredClock_coordinateIterate_eq {f : Vec d → ℝ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (cs : List (Fin d)) (x : Vec d) :
    coordinateIterate cs f x =
      iteratedFDeriv ℝ cs.length f x (centeredClockDirections cs) := by
  induction cs generalizing x with
  | nil => simp [coordinateIterate, iteratedFDeriv_zero_apply]
  | cons k cs ih =>
    have he : coordinateIterate cs f = fun y =>
        iteratedFDeriv ℝ cs.length f y (centeredClockDirections cs) := funext ih
    simp only [coordinateIterate, List.length_cons, centeredClockDirections,
      iteratedFDeriv_succ_apply_left, Fin.cons_zero, Fin.tail_cons]
    rw [he]
    exact fderiv_continuousMultilinear_apply_const_apply
      (hf.differentiable_iteratedFDeriv (m := cs.length) (by
        exact WithTop.coe_lt_coe.mpr (ENat.coe_lt_top _)) x) _ _

private theorem centeredClock_euclidean_unit (k : Fin d) :
    euclideanNorm (unitVector k) = 1 := by
  change Real.sqrt (dotProduct (Pi.single k (1 : ℝ)) (Pi.single k 1)) = 1
  rw [single_dotProduct, Pi.single_eq_same, one_mul, Real.sqrt_one]

private theorem centeredClock_directions_norm (cs : List (Fin d))
    (k : Fin cs.length) : euclideanNorm (centeredClockDirections cs k) = 1 := by
  induction cs with
  | nil => exact Fin.elim0 k
  | cons j cs ih =>
    refine Fin.cases ?_ (fun l => ?_) k
    · exact centeredClock_euclidean_unit j
    · exact ih l

private theorem centeredClock_jet_bound {d : ℕ} {M : ℕ → ℝ} {ω : FieldPair d}
    (hω : IsSmoothWithBounds M ω) (cs : List (Fin d)) (hcs : 1 ≤ cs.length)
    (x : Vec d) : |coordinateIterate cs (fun y => ω.2 y) x| ≤ M cs.length := by
  obtain ⟨A, B, hA, _, hAB, _, hB⟩ := hω.2 cs.length hcs
  rw [centeredClock_coordinateIterate_eq hω.1.2]
  have hb := hB x (centeredClockDirections cs)
  simp only [centeredClock_directions_norm, Finset.prod_const_one, mul_one] at hb
  exact hb.trans (by linarith)

private theorem centeredClock_memLp_top (Q : EnvironmentLaw d Λ r) :
    MemLp (fun ω : FieldPair d => ω.2 0) ∞ (reducedLaw Q) := by
  apply memLp_top_of_bound (by fun_prop) (Real.exp (2 * Λ))
  apply (ae_map_iff Probability.measurable_reduce.aemeasurable
    (measurableSet_le (by fun_prop) measurable_const)).mpr
  filter_upwards [Q.regular] with ω hω
  have h := clockDensity_bounds ω 0 Λ (hω.2.1 0)
  change ‖clockDensity ω 0‖ ≤ _
  simpa only [Real.norm_eq_abs, abs_of_pos (clockDensity_pos ω 0)] using h.2

private theorem centeredClock_jet_step
    {M : ℕ → ℝ} (hs : ∀ᵐ ω ∂reducedLaw Q, IsSmoothWithBounds M ω)
    (cs : List (Fin d))
    (hf : MemLp (iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.2 0))
      2 (reducedLaw Q)) (l : Fin d) :
    ∃ hg : MemLp (iteratedHorizontalDerivative (l :: cs)
      (fun ω : FieldPair d => ω.2 0)) 2 (reducedLaw Q),
      HasHorizontalLpDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
        (hf.toLp _) (hg.toLp _) := by
  let f := iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.2 0)
  have horbit (ω : FieldPair d) : orbit f ω =
      coordinateIterate cs (fun y => ω.2 y) := by
    rw [orbit_iteratedHorizontalDerivative]
    congr 1
    funext y
    simp only [orbit, translate_scalar, add_zero]
  apply timeFlux_horizontal_derivative_of_bounded_orbit
    (reducedLaw_stationary Q) l hf (M (l :: cs).length)
  · filter_upwards [hs] with ω hω
    have hc : ContDiff ℝ (⊤ : ℕ∞) (orbit f ω) := by
      rw [horbit]
      exact contDiff_coordinateIterate hω.1.2 cs
    intro s
    have hd := (hc.differentiable (by simp) (s • unitVector l)).hasFDerivAt.comp_hasDerivAt
      s ((hasDerivAt_id' s).smul_const (unitVector l))
    change HasDerivAt (fun t => orbit f ω (t • unitVector l))
      (horizontalDerivative l f (translate (s • unitVector l) ω)) s
    rw [horizontalDerivative_translate]
    simpa only [Function.comp_def, one_smul, coordinateDerivative] using hd
  · filter_upwards [hs] with ω hω
    intro s
    change |horizontalDerivative l f (translate (s • unitVector l) ω)| ≤ _
    rw [horizontalDerivative_translate, horbit]
    exact centeredClock_jet_bound hω (l :: cs) (by simp) _

/-- Every finite horizontal derivative of an actual reduced clock density is an
L2 observation. Each next raw derivative is its two-sided strong translation
derivative. All smoothness and uniform bounds are derived from the physical
smooth-law assumption; no initial horizontal-domain assumption is added. -/
theorem centeredClock_jets
    {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) :
    ∀ cs : List (Fin d), ∃ hf : MemLp
      (iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.2 0))
      2 (reducedLaw Q),
      ∀ l : Fin d, ∃ hg : MemLp
        (iteratedHorizontalDerivative (l :: cs) (fun ω : FieldPair d => ω.2 0))
        2 (reducedLaw Q),
        HasHorizontalLpDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
          (hf.toLp _) (hg.toLp _) := by
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  have hs := hM Q hQ
  have hmem : ∀ cs : List (Fin d), MemLp
      (iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.2 0))
      2 (reducedLaw Q) := by
    intro cs
    induction cs with
    | nil =>
      exact (centeredClock_memLp_top Q).mono_exponent le_top
    | cons l cs ih => exact (centeredClock_jet_step hs cs ih l).choose
  intro cs
  exact ⟨hmem cs, fun l => centeredClock_jet_step hs cs (hmem cs) l⟩

/-- All finite raw clock jets are essentially bounded under the actual
reduced law, including order zero. This supplies the bounded factors needed
for products in the initial generator graphs. -/
theorem centeredClock_jets_memLp_top {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (cs : List (Fin d)) :
    MemLp (iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.2 0))
      ∞ (reducedLaw Q) := by
  cases cs with
  | nil => exact centeredClock_memLp_top Q
  | cons l cs =>
    obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
      node_eq_u2E_reduced_u2D_bounds_of_deps d D
    apply MemLp.of_bound
      (centeredClock_jets hQ (l :: cs)).choose.aestronglyMeasurable
      (M (l :: cs).length)
    filter_upwards [hM Q hQ] with ω hω
    have he := congrFun (orbit_iteratedHorizontalDerivative (l :: cs)
      (fun η : FieldPair d => η.2 0) ω) 0
    simp only [orbit, translate_zero] at he
    rw [Real.norm_eq_abs, he]
    have ho : orbit (fun η : FieldPair d => η.2 0) ω = fun x => ω.2 x := by
      funext x
      simp only [orbit, translate_scalar, add_zero]
    rw [ho]
    exact centeredClock_jet_bound hω (l :: cs) (by simp) 0

/-- Every raw clock jet has a bound along its entire spatial orbit on
one full-measure event. The order-zero bound comes from actual reduced
clock-density bound; the positive orders use the physical smooth-law bounds. -/
theorem centeredClock_jets_orbit_bounds {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) :
    ∃ B : List (Fin d) → ℝ, (∀ cs, 0 ≤ B cs) ∧
      ∀ cs, ∀ᵐ ω ∂reducedLaw Q, ∀ x : Vec d,
        |orbit (iteratedHorizontalDerivative cs
          (fun η : FieldPair d => η.2 0)) ω x| ≤ B cs := by
  obtain ⟨K, A, B, hK, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity Q.ellipticity_parameter
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  refine ⟨fun cs => if cs = [] then K else |M cs.length|, ?_, ?_⟩
  · intro cs
    dsimp only
    split_ifs
    · exact zero_le_one.trans hK
    · exact abs_nonneg _
  · intro cs
    filter_upwards [(hb d D.dependenceRange Q).2.2, hM Q hQ] with ω he hs
    intro x
    rw [orbit_iteratedHorizontalDerivative]
    have ho : orbit (fun η : FieldPair d => η.2 0) ω = fun y => ω.2 y := by
      funext y
      simp only [orbit, translate_scalar, add_zero]
    rw [ho]
    cases cs with
    | nil =>
      simp only [coordinateIterate, ↓reduceIte]
      have hpos : 0 < ω.2 x := lt_of_lt_of_le
        (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hK)) (he.2.1 x).1
      rw [abs_of_pos hpos]
      exact (he.2.1 x).2
    | cons l cs =>
      simp only [List.cons_ne_nil, ↓reduceIte]
      exact (centeredClock_jet_bound hs (l :: cs) (by simp) x).trans
        (le_abs_self _)

private theorem centeredClock_jet_curve {ω : FieldPair d} {M : ℕ → ℝ}
    (hω : IsSmoothWithBounds M ω) (l : Fin d) (cs : List (Fin d)) (s : ℝ) :
    HasDerivAt (fun t : ℝ => iteratedHorizontalDerivative cs
      (fun η : FieldPair d => η.2 0) (translate (t • unitVector l) ω))
      (iteratedHorizontalDerivative (l :: cs)
        (fun η : FieldPair d => η.2 0) (translate (s • unitVector l) ω)) s := by
  let f := iteratedHorizontalDerivative cs (fun η : FieldPair d => η.2 0)
  have horbit : orbit f ω = coordinateIterate cs (fun y => ω.2 y) := by
    rw [orbit_iteratedHorizontalDerivative]
    congr 1
    funext y
    simp only [orbit, translate_scalar, add_zero]
  have hc : ContDiff ℝ (⊤ : ℕ∞) (orbit f ω) := by
    rw [horbit]
    exact contDiff_coordinateIterate hω.1.2 cs
  have hd := (hc.differentiable (by simp) (s • unitVector l)).hasFDerivAt.comp_hasDerivAt
    s ((hasDerivAt_id' s).smul_const (unitVector l))
  change HasDerivAt (fun t => orbit f ω (t • unitVector l))
    (horizontalDerivative l f (translate (s • unitVector l) ω)) s
  rw [horizontalDerivative_translate]
  simpa only [Function.comp_def, one_smul, coordinateDerivative] using hd


private def centeredEquationsPair (f : Lp ℂ 2 (reducedLaw Q)) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing (reducedLaw Q) 2 2 f

private theorem centeredEquationsPair_apply (f g : Lp ℂ 2 (reducedLaw Q)) :
    centeredEquationsPair f g = ∫ ω, f ω * g ω ∂reducedLaw Q := by
  rw [centeredEquationsPair, ContinuousLinearMap.lpPairing_eq_integral]
  rfl

private theorem centeredEquations_coefficient_jet_curve {ω : FieldPair d} {M : ℕ → ℝ}
    (hω : IsSmoothWithBounds M ω) (j k l : Fin d) (cs : List (Fin d)) (s : ℝ) :
    HasDerivAt (fun t : ℝ => iteratedHorizontalDerivative cs
      (fun η : FieldPair d => η.1 0 j k) (translate (t • unitVector l) ω))
      (iteratedHorizontalDerivative (l :: cs)
        (fun η : FieldPair d => η.1 0 j k) (translate (s • unitVector l) ω)) s := by
  let f := iteratedHorizontalDerivative cs (fun η : FieldPair d => η.1 0 j k)
  have horbit : orbit f ω = coordinateIterate cs (fun y => ω.1 y j k) := by
    rw [orbit_iteratedHorizontalDerivative]
    congr 1
    funext y
    simp only [orbit, translate_matrix, add_zero]
  have hc : ContDiff ℝ (⊤ : ℕ∞) (orbit f ω) := by
    rw [horbit]
    exact contDiff_coordinateIterate (hω.1.1 j k) cs
  have hd := (hc.differentiable (by simp) (s • unitVector l)).hasFDerivAt.comp_hasDerivAt
    s ((hasDerivAt_id' s).smul_const (unitVector l))
  change HasDerivAt (fun t => orbit f ω (t • unitVector l))
    (horizontalDerivative l f (translate (s • unitVector l) ω)) s
  rw [horizontalDerivative_translate]
  simpa only [Function.comp_def, one_smul, coordinateDerivative] using hd

private theorem centeredClock_jet_products {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k : Fin d) (cs bs : List (Fin d)) :
    let f := iteratedHorizontalDerivative cs (fun ω : FieldPair d => ω.1 0 j k)
    let g := iteratedHorizontalDerivative bs (fun ω : FieldPair d => ω.2 0)
    ∃ hf : MemLp (fun ω => f ω * g ω) 2 (reducedLaw Q),
      ∀ l : Fin d, ∃ hg : MemLp (fun ω =>
        iteratedHorizontalDerivative (l :: cs) (fun η : FieldPair d => η.1 0 j k) ω * g ω +
          f ω * iteratedHorizontalDerivative (l :: bs)
            (fun η : FieldPair d => η.2 0) ω) 2 (reducedLaw Q),
        HasHorizontalLpDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
          (hf.toLp _) (hg.toLp _) := by
  dsimp only
  have hf : MemLp (fun ω =>
      iteratedHorizontalDerivative cs (fun η : FieldPair d => η.1 0 j k) ω *
        iteratedHorizontalDerivative bs (fun η : FieldPair d => η.2 0) ω)
      2 (reducedLaw Q) :=
    (timeFlux_coefficient_jets_memLp_top hQ j k cs).fun_mul
      (centeredClock_jets hQ bs).choose
  refine ⟨hf, ?_⟩
  intro l
  obtain ⟨C, hC, hCb⟩ := timeFlux_coefficient_jets_orbit_bounds hQ j k
  obtain ⟨E, hE, hEb⟩ := centeredClock_jets_orbit_bounds hQ
  obtain ⟨M, _, hM⟩ := node_eq_u2E_reduced_u2D_bounds_u23_derivatives_of_deps
    node_eq_u2E_reduced_u2D_bounds_of_deps d D
  apply timeFlux_horizontal_derivative_of_bounded_orbit (reducedLaw_stationary Q) l hf
    (C (l :: cs) * E bs + C cs * E (l :: bs))
  · filter_upwards [hM Q hQ] with ω hω
    intro s
    exact (centeredEquations_coefficient_jet_curve hω j k l cs s).mul
      (centeredClock_jet_curve hω l bs s)
  · filter_upwards [hCb (l :: cs), hCb cs, hEb (l :: bs), hEb bs]
      with ω h1 h2 h3 h4
    intro s
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul (h1 _) (h4 _) (abs_nonneg _) (hC _)
    · rw [abs_mul]
      exact mul_le_mul (h2 _) (h3 _) (abs_nonneg _) (hC _)

private def centeredClockJet {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (cs : List (Fin d)) :
    Lp ℂ 2 (reducedLaw Q) :=
  Complex.ofRealCLM.compLpL 2 (reducedLaw Q)
    ((centeredClock_jets hQ cs).choose.toLp _)

private theorem centeredClockJet_ae {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (cs : List (Fin d)) :
    centeredClockJet hQ cs =ᵐ[reducedLaw Q]
      (fun ω => (iteratedHorizontalDerivative cs (fun η : FieldPair d => η.2 0) ω : ℂ)) := by
  filter_upwards [Complex.ofRealCLM.coeFn_compLpL
    ((centeredClock_jets hQ cs).choose.toLp _),
    (centeredClock_jets hQ cs).choose.coeFn_toLp] with ω h1 h2
  exact h1.trans (congrArg Complex.ofReal h2)

private theorem centeredClockJet_derivative {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (cs : List (Fin d)) (l : Fin d) :
    HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
      (centeredClockJet hQ cs) (centeredClockJet hQ (l :: cs)) :=
  hasComplexHorizontalDerivative_ofReal
    ((centeredClock_jets hQ cs).choose_spec l).choose_spec

private theorem centeredEquations_sum_ae (μ : Measure (FieldPair d))
    (s : Finset (Fin d)) (f : Fin d → Lp ℂ 2 μ) :
    (∑ j ∈ s, f j : Lp ℂ 2 μ) =ᵐ[μ] fun ω => ∑ j ∈ s, f j ω := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty, Pi.zero_apply] using! Lp.coeFn_zero ℂ 2 μ
  | @insert j s hj ih =>
    simp only [Finset.sum_insert hj]
    filter_upwards [Lp.coeFn_add (f j) (∑ k ∈ s, f k), ih] with ω h1 h2
    simpa only [Pi.add_apply, h2] using h1

private theorem centeredClock_coefficient_mul_jet_derivative {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) (j k l : Fin d) (cs : List (Fin d)) :
    ∃ H : Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) l
        (complexCoefficientMul Q j k (centeredClockJet hQ cs)) H := by
  obtain ⟨hf, hh⟩ := centeredClock_jet_products hQ j k [] cs
  obtain ⟨hg, hd⟩ := hh l
  have he : complexCoefficientMul Q j k (centeredClockJet hQ cs) =
      Complex.ofRealCLM.compLpL 2 (reducedLaw Q) (hf.toLp _) := by
    apply Lp.ext
    filter_upwards [complexCoefficientMul_coe Q j k (centeredClockJet hQ cs),
      centeredClockJet_ae hQ cs,
      Complex.ofRealCLM.coeFn_compLpL (hf.toLp _), hf.coeFn_toLp] with ω h1 h2 h3 h4
    simp only [h1, h2, h3, h4, Complex.ofRealCLM_apply, Complex.ofReal_mul]
    rfl
  rw [he]
  exact ⟨_, hasComplexHorizontalDerivative_ofReal hd⟩

private theorem centeredEquations_generator_of_flux_derivatives
    {f : Lp ℂ 2 (reducedLaw Q)} {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G)
    (hF : ∀ j k : Fin d, ∃ H : Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j
        (complexCoefficientMul Q j k (G k)) H) :
    ∃ g : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i ζ f g := by
  classical
  choose H hH using hF
  let g : Lp ℂ 2 (reducedLaw Q) :=
    (1 / 2 : ℂ) • (∑ j, ∑ k, H j k) + ζ • ∑ j, complexCoefficientMul Q j i (G j)
  refine ⟨g, G, hG, ?_⟩
  intro v V hV
  have hp (j k : Fin d) : centeredEquationsPair v (H j k) =
      -(∫ ω, (ω.1 0 j k : ℂ) * G k ω * V j ω ∂reducedLaw Q) := by
    rw [centeredEquationsPair_apply]
    have hb := (complexHorizontalDerivatives_integration_by_parts (hH j k) (hV j)).2.2
    calc
      _ = ∫ ω, H j k ω * v ω ∂reducedLaw Q := by
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun ω => mul_comm _ _
      _ = _ := hb
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [complexCoefficientMul_coe Q j k (G k)] with ω hω
        rw [hω]
  have hd : centeredEquationsPair v (∑ j, complexCoefficientMul Q j i (G j)) =
      ∫ ω, (∑ j, (ω.1 0 j i : ℂ) * G j ω) * v ω ∂reducedLaw Q := by
    rw [centeredEquationsPair_apply]
    apply integral_congr_ae
    filter_upwards [centeredEquations_sum_ae (reducedLaw Q) Finset.univ
        (fun j => complexCoefficientMul Q j i (G j)),
      ae_all_iff.mpr (fun j => complexCoefficientMul_coe Q j i (G j))] with ω h1 h2
    simp only [h1, h2]
    exact mul_comm _ _
  have hi (j k : Fin d) : Integrable
      (fun ω => (ω.1 0 j k : ℂ) * G k ω * V j ω) (reducedLaw Q) := by
    have hm := (Lp.memLp (complexCoefficientMul Q j k (G k))).integrable_mul (Lp.memLp (V j))
    apply hm.congr
    filter_upwards [complexCoefficientMul_coe Q j k (G k)] with ω hω
    simp only [Pi.mul_apply, hω]
  have he : (∫ ω, g ω * v ω ∂reducedLaw Q) = centeredEquationsPair v g := by
    simp only [centeredEquationsPair_apply, mul_comm]
  rw [he]
  change centeredEquationsPair v ((1 / 2 : ℂ) • (∑ j, ∑ k, H j k) +
    ζ • ∑ j, complexCoefficientMul Q j i (G j)) = _
  rw [map_add, map_smul, map_smul, hd]
  simp only [map_sum, hp, smul_eq_mul, Finset.sum_neg_distrib]
  rw [integral_finset_sum _ (fun j _ => integrable_finset_sum _ (fun k _ => hi j k))]
  simp_rw [integral_finset_sum _ (fun k _ => hi _ k)]
  ring

/-- The actual clock observation belongs to the full forward generator
at every complex force, as a consequence of the physical smooth-law bounds. -/
theorem centeredEquations_clock_initial_generator {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    (hQ : HasSmoothBounds D Q) {μ : Lp ℂ 2 (reducedLaw Q)}
    (hμ : IsReducedClockObservation Q μ) :
    ∃ g : Lp ℂ 2 (reducedLaw Q), IsComplexGeneratorPair Q i ζ μ g := by
  have he : μ = centeredClockJet hQ [] := by
    apply Lp.ext
    exact hμ.trans (centeredClockJet_ae hQ []).symm
  rw [he]
  exact centeredEquations_generator_of_flux_derivatives
    (fun l => centeredClockJet_derivative hQ [] l)
    (fun j k => centeredClock_coefficient_mul_jet_derivative hQ j k j [k])


/-- Rewriting the actual forward generator with its centered anisotropic flux
retains exactly the mean-subtracted force source on a common spatial event. -/
private theorem centeredEquations_forward_equation {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    {Q : EnvironmentLaw d Λ r} (ν : EndpointIndex d) (hν : ν ≠ .inr true)
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a) {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)}
    (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ ζ f g) :
    ∃ G J, IsEndpointWeakFlux hd Q ν ζ a (centeredComplexLp Q f) G J ∧
      ∀ᵐ ω ∂reducedLaw Q,
        ∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
          (∫ x, centeredComplexLp Q g (translate x ω) * (φ x : ℂ)) +
            (1 / 2 : ℂ) * (∫ x, ∑ j : Fin d, ∑ k : Fin d,
              (homogenizedCoefficient Q j k : ℂ) * G k (translate x ω) *
                (coordinateDerivative j φ x : ℂ)) -
            ζ * (∫ x, (∑ j : Fin d,
              (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) *
                G j (translate x ω)) * (φ x : ℂ)) =
          -(1 / 2 : ℂ) * (∫ x, ∑ j : Fin d,
            J j (translate x ω) * (coordinateDerivative j φ x : ℂ)) +
            ζ * (∫ x, (J ⟨0, by omega⟩ (translate x ω) -
              ∫ η, J ⟨0, by omega⟩ η ∂reducedLaw Q) * (φ x : ℂ)) := by
  classical
  let i : Fin d := ⟨0, by omega⟩
  let A := homogenizedCoefficient Q
  have hgraph := hfg
  obtain ⟨G, hG, _⟩ := hgraph
  obtain ⟨J, hJ⟩ := forward_weakFlux hd Q ν hν ζ a ha _ G hG.centered
  have hraw (j : Fin d) : (J j : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
      ∑ k, ((ω.1 0 j k : ℂ) - (A j k : ℂ)) * G k ω := by
    filter_upwards [hJ.2 j, ae_all_iff.mpr (fun k => ha j k)] with ω hj haω
    rw [hj]
    apply Finset.sum_congr rfl
    intro k _
    rcases ν with v | b
    · simp only [haω k, sub_zero]
      rfl
    · cases b
      · simp only [haω k, sub_zero]
        rfl
      · exact (hν rfl).elim
  have hcol : (J i : FieldPair d → ℂ) =ᵐ[reducedLaw Q] fun ω =>
      (∑ j, (ω.1 0 j i : ℂ) * G j ω) - ∑ j, (A j i : ℂ) * G j ω := by
    filter_upwards [hraw i, Correctors.ae_reducedEnvironmentLaw_origin_elliptic Q]
      with ω hj hω
    rw [hj, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    have hs : ω.1 0 i j = ω.1 0 j i := by
      exact congrFun (congrFun (hω 0).1 j) i
    have hA : A i j = A j i := by
      exact congrFun (congrFun (homogenizedCoefficient_transpose (Q := Q)) j) i
    rw [hs, hA, sub_mul]
  have hmean : (∫ η, g η ∂reducedLaw Q) = ζ * ∫ η, J i η ∂reducedLaw Q := by
    obtain ⟨H, hH, hm⟩ := hfg.integral_eq
    have he : H = G := hH.unique hG
    subst H
    rw [hm]
    congr 1
    rw [integral_congr_ae hcol]
    have hb : Integrable (fun ω => ∑ j, (ω.1 0 j i : ℂ) * G j ω)
        (reducedLaw Q) := by
      apply integrable_finset_sum
      intro j _
      exact ((Lp.memLp (complexCoefficientMul Q j i (G j))).ae_eq
        (complexCoefficientMul_coe Q j i (G j))).integrable (by norm_num)
    have hA : Integrable (fun ω => ∑ j, (A j i : ℂ) * G j ω)
        (reducedLaw Q) := integrable_finset_sum _ fun j _ =>
      ((Lp.memLp (G j)).integrable (by norm_num)).const_mul _
    rw [integral_sub hb hA, integral_finset_sum _ (fun j _ =>
      ((Lp.memLp (G j)).integrable (by norm_num)).const_mul _)]
    simp only [integral_const_mul, fun j => (hG j).integral_eq_zero,
      mul_zero, Finset.sum_const_zero, sub_zero]
    rfl
  have hsp (j : Fin d) := ae_complex_spatial_orbit_congr (reducedLaw Q)
    (reducedLaw_stationary Q) (Lp.stronglyMeasurable (J j)).measurable
    (by fun_prop) (hraw j)
  have hcsp := ae_complex_spatial_orbit_congr (reducedLaw Q)
    (reducedLaw_stationary Q) (Lp.stronglyMeasurable (J i)).measurable
    (by fun_prop) hcol
  have hvsp := ae_complex_spatial_orbit_congr (reducedLaw Q)
    (reducedLaw_stationary Q) (Lp.stronglyMeasurable (centeredComplexLp Q g)).measurable
    (by fun_prop) (coeFn_centeredComplexLp Q g)
  refine ⟨G, J, hJ, ?_⟩
  filter_upwards [hfg.spatial_flux_all_tests hG, ae_all_iff.mpr hsp, hcsp, hvsp,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) g,
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (G j)),
    ae_all_iff.mpr (fun j => ae_complex_orbit_memLp_on_all_compacts
      (reducedLaw Q) (reducedLaw_stationary Q) (J j))] with ω he hr hc hv hg hGl hJl
  intro φ hφ hφc
  have he := he φ hφ hφc
  have hdc (j : Fin d) : Continuous (coordinateDerivative j φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hGtest (j k : Fin d) := integrable_spatial_mul_test (hGl k) (hdc j)
    (hφc.fderiv_apply ℝ (unitVector j))
  have hJtest (j : Fin d) := integrable_spatial_mul_test (hJl j) (hdc j)
    (hφc.fderiv_apply ℝ (unitVector j))
  have hGj (j : Fin d) := integrable_spatial_mul_test (hGl j) hφ.continuous hφc
  have hJi := integrable_spatial_mul_test (hJl i) hφ.continuous hφc
  have hgt := integrable_spatial_mul_test hg hφ.continuous hφc
  let B : Vec d → ℂ := fun x => ∑ j : Fin d, ∑ k : Fin d,
    (A j k : ℂ) * G k (translate x ω) * (coordinateDerivative j φ x : ℂ)
  let C : Vec d → ℂ := fun x => (∑ j : Fin d,
    (A j i : ℂ) * G j (translate x ω)) * (φ x : ℂ)
  let F : Vec d → ℂ := fun x => ∑ j : Fin d,
    J j (translate x ω) * (coordinateDerivative j φ x : ℂ)
  have hB : Integrable B := integrable_finset_sum _ fun j _ =>
    integrable_finset_sum _ fun k _ => by
      simpa only [mul_assoc] using (hGtest j k).const_mul (A j k : ℂ)
  have hC : Integrable C := by
    simp only [C, Finset.sum_mul]
    exact integrable_finset_sum _ fun j _ => by
      simpa only [mul_assoc] using (hGj j).const_mul (A j i : ℂ)
  have hF : Integrable F := integrable_finset_sum _ fun j _ => hJtest j
  have hsplit : (∫ x, ∑ j : Fin d,
      (∑ k : Fin d, (ω.1 x j k : ℂ) * G k (translate x ω)) *
        (coordinateDerivative j φ x : ℂ)) = (∫ x, F x) + (∫ x, B x) := by
    rw [← integral_add hF hB]
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hr] with x hx
    simp only [translate_matrix, add_zero] at hx
    dsimp only [F, B]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rw [hx j]
    simp only [sub_mul, Finset.sum_sub_distrib, Finset.sum_mul]
    ring
  have hcsplit : (∫ x, (∑ j : Fin d,
      (ω.1 x j i : ℂ) * G j (translate x ω)) * (φ x : ℂ)) =
      (∫ x, J i (translate x ω) * (φ x : ℂ)) + ∫ x, C x := by
    rw [← integral_add hJi hC]
    apply integral_congr_ae
    filter_upwards [hc] with x hx
    simp only [translate_matrix, add_zero] at hx
    dsimp only [C]
    rw [hx]
    ring
  have hφi : Integrable (fun x => (φ x : ℂ)) :=
    (hφ.continuous.integrable_of_hasCompactSupport hφc).ofReal
  have hvs : (∫ x, centeredComplexLp Q g (translate x ω) * (φ x : ℂ)) =
      (∫ x, g (translate x ω) * (φ x : ℂ)) -
      ζ * (∫ η, J i η ∂reducedLaw Q) * (∫ x, (φ x : ℂ)) := by
    have hv' : (fun x => centeredComplexLp Q g (translate x ω) * (φ x : ℂ)) =ᵐ[volume]
        (fun x => (g (translate x ω) - ∫ η, g η ∂reducedLaw Q) * (φ x : ℂ)) := by
      filter_upwards [hv] with x hx
      rw [hx]
    rw [integral_congr_ae hv']
    simp_rw [sub_mul]
    rw [integral_sub hgt (hφi.const_mul _), integral_const_mul, hmean]
  have hJs : (∫ x, (J i (translate x ω) - ∫ η, J i η ∂reducedLaw Q) *
      (φ x : ℂ)) = (∫ x, J i (translate x ω) * (φ x : ℂ)) -
      (∫ η, J i η ∂reducedLaw Q) * (∫ x, (φ x : ℂ)) := by
    simp_rw [sub_mul]
    rw [integral_sub hJi (hφi.const_mul _), integral_const_mul]
  rw [hsplit, hcsplit] at he
  rw [hvs, hJs]
  change _ + (1 / 2 : ℂ) * (∫ x, B x) - ζ * (∫ x, C x) = _
  linear_combination he


private theorem centeredEquations_forward_centered_hasDerivAt
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) :
    HasDerivAt (fun s : ℝ => centeredComplexLp Q (P s.toNNReal f))
      (centeredComplexLp Q (P t g)) (t : ℝ) := by
  have he := ((centeredComplexLpCLM Q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    (t : ℝ) (centeredEquations_forward_hasDerivAt hP hfg t ht)
  change HasDerivAt (fun s : ℝ => centeredComplexLpCLM Q (P s.toNNReal f))
    (centeredComplexLpCLM Q (P t g)) (t : ℝ) at he
  simpa only [centeredComplexLpCLM_apply] using he

/-- The actual centered velocity and clock fields and the conservative
transpose satisfy the displayed equations at every positive time. -/
theorem node_e_u3A_centered_u2D_equations_of_deps :
    node_e_u3A_centered_u2D_equationsStmt := by
  intro d hd D Q hQ β a μ hβ ha hμ ζ P T hP hT ν t ht
  rcases ν with j | b
  · dsimp only [indexedEndpoint]
    obtain ⟨g, hg⟩ := timeFlux_forward_initial_generator hβ ha j
    obtain ⟨G, J, hJ, he⟩ := centeredEquations_forward_equation hd (.inl j)
      (by simp) ha (hP.map_generator hg t)
    refine ⟨G, J, centeredComplexLp Q (P t g), hJ, ?_, ?_, ?_⟩
    · exact centeredEquations_forward_centered_hasDerivAt hP hg t ht
    · simp
    · simpa only [endpointDriftSign, Complex.ofReal_one, one_mul] using he
  · cases b
    · dsimp only [indexedEndpoint]
      obtain ⟨g, hg⟩ := centeredEquations_clock_initial_generator
        (i := ⟨0, by omega⟩) (ζ := ζ) hQ hμ
      have hc (r : ℝ≥0) : centeredComplexLp Q (P r (ζ • μ)) = clockEndpoint Q ζ P μ r := by
        calc
          _ = centeredComplexLpCLM Q (P r (ζ • μ)) :=
            (centeredComplexLpCLM_apply Q _).symm
          _ = ζ • centeredComplexLpCLM Q (P r μ) := by rw [map_smul, map_smul]
          _ = _ := by rw [centeredComplexLpCLM_apply]; rfl
      obtain ⟨G, J, hJ, he⟩ := centeredEquations_forward_equation hd (.inr false)
        (by simp) ha (hP.map_generator (hg.smul ζ) t)
      rw [hc] at hJ
      refine ⟨G, J, centeredComplexLp Q (P t (ζ • g)), hJ, ?_, ?_, ?_⟩
      · simpa only [hc] using
          centeredEquations_forward_centered_hasDerivAt hP (hg.smul ζ) t ht
      · simp
      · simpa only [endpointDriftSign, Complex.ofReal_one, one_mul] using he
    · dsimp only [indexedEndpoint]
      obtain ⟨G, J, V, hJ, hder, hmean, he⟩ := centeredEquations_transpose hd hβ ha hP hT t ht
      refine ⟨G, J, V, hJ, hder, fun _ => hmean, ?_⟩
      simpa only [endpointDriftSign, Complex.ofReal_neg, Complex.ofReal_one,
        neg_one_mul, neg_mul, sub_neg_eq_add, add_zero, one_mul] using he

end EinsteinFull.Blueprint
