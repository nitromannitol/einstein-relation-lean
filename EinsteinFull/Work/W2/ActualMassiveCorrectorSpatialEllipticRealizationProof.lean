import EinsteinFull.Calculus.ComplexGeneratorSpatialSupport
import EinsteinFull.Work.W2.MassiveCorrectorGradientSupport
import EinsteinRelation.Mobility.DriftBoundPointwise

/-!
# Actual massive correctors as spatial elliptic weak solutions

The countable dense-test argument below extends the scalar orbit argument of
`EinsteinRelation.Correctors.CommonScalarOrbitTests` to an inhomogeneous
complex divergence. All representatives are literal translated L2 fields.
-/

open MeasureTheory Filter Set
open scoped Topology BigOperators ENNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.Correctors.StationaryCurlRealization

namespace MassiveSpatial
variable {d : ℕ}

private abbrev TestSpace (d : ℕ) :=
  (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) × Lp ℂ 2 (volume : Measure (Vec d))

private theorem derivative_continuous (j : Fin d) (ψ : SpatialTest d) :
    Continuous (coordinateDerivative j ψ) :=
  (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const

private def testPair (ψ : SpatialTest d) : TestSpace d :=
  ((fun j => ((Complex.continuous_ofReal.comp (derivative_continuous j ψ)).memLp_of_hasCompactSupport
    ((ψ.hasCompactSupport.fderiv_apply ℝ (unitVector j)).comp_left rfl)).toLp _),
    ((Complex.continuous_ofReal.comp ψ.contDiff.continuous).memLp_of_hasCompactSupport
      (ψ.hasCompactSupport.comp_left rfl)).toLp _)

private def testRange (d n : ℕ) : Set (TestSpace d) :=
  {p | ∃ ψ : SpatialTest d,
    tsupport (ψ : Vec d → ℝ) ⊆ Metric.closedBall 0 ((n : ℝ) + 1) ∧ testPair ψ = p}

private theorem exists_dense_tests (d n : ℕ) :
    ∃ D : Set (testRange d n), D.Countable ∧ Dense D := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  letI : SecondCountableTopology (Lp ℂ 2 (volume : Measure (Vec d))) := inferInstance
  letI : SecondCountableTopology (Fin d → Lp ℂ 2 (volume : Measure (Vec d))) := inferInstance
  letI : SecondCountableTopology (TestSpace d) := inferInstance
  exact TopologicalSpace.exists_countable_dense _

private def denseTests (d n : ℕ) : Set (testRange d n) :=
  (exists_dense_tests d n).choose

private def denseTest (n : ℕ) (p : denseTests d n) : SpatialTest d := p.1.2.choose

private theorem denseTest_spec (n : ℕ) (p : denseTests d n) :
    tsupport (denseTest n p : Vec d → ℝ) ⊆ Metric.closedBall 0 ((n : ℝ) + 1) ∧
      testPair (denseTest n p) = p.1.1 := p.1.2.choose_spec

private def localLp (f : Vec d → ℂ) (n : ℕ)
    (hf : MemLp f 2 (volume.restrict (Metric.closedBall 0 ((n : ℝ) + 1)))) :
    Lp ℂ 2 (volume : Measure (Vec d)) :=
  ((memLp_indicator_iff_restrict (isCompact_closedBall (0 : Vec d) _).measurableSet).mpr hf).toLp _

private def pairing (F : Fin d → Vec d → ℂ) (h : Vec d → ℂ) (n : ℕ)
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Metric.closedBall 0 ((n : ℝ) + 1))))
    (hh : MemLp h 2 (volume.restrict (Metric.closedBall 0 ((n : ℝ) + 1)))) :
    TestSpace d →L[ℂ] ℂ :=
  (∑ j, (innerSL ℂ (star (localLp (F j) n (hF j)))).comp
    ((ContinuousLinearMap.proj j).comp (ContinuousLinearMap.fst ℂ _ _))) +
  (innerSL ℂ (star (localLp h n hh))).comp (ContinuousLinearMap.snd ℂ _ _)

private theorem local_inner_test (f a : Vec d → ℂ) (n : ℕ)
    (hf : MemLp f 2 (volume.restrict (Metric.closedBall 0 ((n : ℝ) + 1))))
    (ha : MemLp a 2 volume)
    (hsupp : ∀ x ∉ Metric.closedBall (0 : Vec d) ((n : ℝ) + 1), a x = 0) :
    inner ℂ (star (localLp f n hf)) (ha.toLp a) = ∫ x, f x * a x := by
  have hl : localLp f n hf =ᵐ[volume]
      (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)).indicator f :=
    ((memLp_indicator_iff_restrict (isCompact_closedBall (0 : Vec d) _).measurableSet).mpr hf).coeFn_toLp
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hl, ha.coeFn_toLp, Lp.coeFn_star (localLp f n hf)] with x hxl hxa hxs
  change (star (localLp f n hf) : Lp ℂ 2 volume) x = star (localLp f n hf x) at hxs
  rw [hxs, hxl, hxa, RCLike.inner_apply]
  simp only [← starRingEnd_apply, starRingEnd_self_apply]
  by_cases hx : x ∈ Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)
  · simp only [Set.indicator_of_mem hx, mul_comm]
  · simp only [Set.indicator_of_notMem hx, hsupp x hx, mul_zero]

private theorem pairing_test (F : Fin d → Vec d → ℂ) (h : Vec d → ℂ) (n : ℕ)
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Metric.closedBall 0 ((n : ℝ) + 1))))
    (hh : MemLp h 2 (volume.restrict (Metric.closedBall 0 ((n : ℝ) + 1))))
    (ψ : SpatialTest d)
    (hsupp : tsupport (ψ : Vec d → ℝ) ⊆ Metric.closedBall 0 ((n : ℝ) + 1)) :
    pairing F h n hF hh (testPair ψ) =
      (∑ j, ∫ x, F j x * (coordinateDerivative j ψ x : ℂ)) +
        ∫ x, h x * (ψ x : ℂ) := by
  simp only [pairing, ContinuousLinearMap.add_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply,
    innerSL_apply_apply]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    change inner ℂ (star (localLp (F j) n (hF j))) ((testPair ψ).1 j) = _
    apply local_inner_test (F j) _ n (hF j)
      ((Complex.continuous_ofReal.comp (derivative_continuous j ψ)).memLp_of_hasCompactSupport
        ((ψ.hasCompactSupport.fderiv_apply ℝ (unitVector j)).comp_left rfl))
    intro x hx
    simp only [Function.comp_apply, coordinateDerivative,
      fderiv_of_notMem_tsupport ℝ (fun ht => hx (hsupp ht)), ContinuousLinearMap.zero_apply,
      Complex.ofReal_zero]
  · change inner ℂ (star (localLp h n hh)) (testPair ψ).2 = _
    apply local_inner_test h _ n hh
      ((Complex.continuous_ofReal.comp ψ.contDiff.continuous).memLp_of_hasCompactSupport
        (ψ.hasCompactSupport.comp_left rfl))
    intro x hx
    simp only [Function.comp_apply]
    rw [image_eq_zero_of_notMem_tsupport (fun ht => hx (hsupp ht)), Complex.ofReal_zero]

/-- A locally L2 inhomogeneous complex divergence has one event for all smooth
compact spatial tests. The dense set includes every gradient coordinate. -/
theorem ae_allTests_of_fixedTest {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (F : A → Fin d → Vec d → ℂ) (h : A → Vec d → ℂ)
    (hloc : ∀ᵐ ω ∂μ, ∀ K : Set (Vec d), IsCompact K →
      (∀ j, MemLp (F ω j) 2 (volume.restrict K)) ∧ MemLp (h ω) 2 (volume.restrict K))
    (hfixed : ∀ ψ : SpatialTest d, ∀ᵐ ω ∂μ,
      (∑ j, ∫ x, F ω j x * (coordinateDerivative j ψ x : ℂ)) +
        (∫ x, h ω x * (ψ x : ℂ)) = 0) :
    ∀ᵐ ω ∂μ, ∀ ψ : SpatialTest d,
      (∑ j, ∫ x, F ω j x * (coordinateDerivative j ψ x : ℂ)) +
        (∫ x, h ω x * (ψ x : ℂ)) = 0 := by
  have hdense : ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ p : denseTests d n,
      (∑ j, ∫ x, F ω j x * (coordinateDerivative j (denseTest n p) x : ℂ)) +
        (∫ x, h ω x * (denseTest n p x : ℂ)) = 0 := by
    apply ae_all_iff.mpr
    intro n
    letI : Countable (denseTests d n) := (exists_dense_tests d n).choose_spec.1.to_subtype
    exact ae_all_iff.mpr fun p => hfixed (denseTest n p)
  filter_upwards [hloc, hdense] with ω hω hD
  intro ψ
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp
    ψ.hasCompactSupport.isCompact.isBounded
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hsupp : tsupport (ψ : Vec d → ℝ) ⊆ Metric.closedBall 0 ((n : ℝ) + 1) :=
    hR.trans (Metric.closedBall_subset_closedBall (le_trans hn.le (by norm_num)))
  obtain ⟨hF, hh⟩ := hω _ (isCompact_closedBall (0 : Vec d) ((n : ℝ) + 1))
  let P : testRange d n → ℂ := fun p => pairing (F ω) (h ω) n hF hh p.1
  have hP : Continuous P := (pairing (F ω) (h ω) n hF hh).continuous.comp continuous_subtype_val
  have hsub : denseTests d n ⊆ {p : testRange d n | P p = 0} := by
    intro p hp
    let q : denseTests d n := ⟨p, hp⟩
    have hs := denseTest_spec n q
    change pairing (F ω) (h ω) n hF hh p.1 = 0
    rw [← hs.2, pairing_test (F ω) (h ω) n hF hh (denseTest n q) hs.1]
    exact hD n q
  have hcl := closure_minimal hsub (isClosed_eq hP continuous_const)
  have hd : Dense (denseTests d n) := (exists_dense_tests d n).choose_spec.2
  rw [hd.closure_eq] at hcl
  have hres := hcl (Set.mem_univ (⟨testPair ψ, ψ, hsupp, rfl⟩ : testRange d n))
  change pairing (F ω) (h ω) n hF hh (testPair ψ) = 0 at hres
  rwa [pairing_test (F ω) (h ω) n hF hh ψ hsupp] at hres

end MassiveSpatial

/-- Measurable stationary L2 weak divergences realize their full spatial
inhomogeneous equation on one event shared by all compact smooth tests. -/
theorem ae_complex_spatial_divergence_allTests {d : ℕ}
    (μ : Measure (FieldPair d)) [IsProbabilityMeasure μ] (hμ : IsStationary μ)
    (F : Fin d → FieldPair d → ℂ) (h : FieldPair d → ℂ)
    (hFm : ∀ j, Measurable (F j)) (hhm : Measurable h)
    (hF : ∀ j, MemLp (F j) 2 μ) (hh : MemLp h 2 μ)
    (hw : ∀ (v : Lp ℂ 2 μ) (V : Fin d → Lp ℂ 2 μ),
      HasComplexHorizontalGradient μ hμ v V →
      (∫ ω, ∑ j, F j ω * V j ω ∂μ) = -(∫ ω, h ω * v ω ∂μ)) :
    ∀ᵐ ω ∂μ, ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, h (translate x ω) * (φ x : ℂ)) =
        -(∫ x, ∑ j, F j (translate x ω) * (coordinateDerivative j φ x : ℂ)) := by
  have hloc := (ae_all_iff.mpr fun j =>
    ae_complex_function_orbit_memLp_on_all_compacts μ hμ (hFm j) (hF j)).and
      (ae_complex_function_orbit_memLp_on_all_compacts μ hμ hhm hh)
  have hlocal : ∀ᵐ ω ∂μ, ∀ K : Set (Vec d), IsCompact K →
      (∀ j, MemLp (fun x => F j (translate x ω)) 2 (volume.restrict K)) ∧
      MemLp (fun x => h (translate x ω)) 2 (volume.restrict K) := by
    filter_upwards [hloc] with ω hω
    exact fun K hK => ⟨fun j => hω.1 j K hK, hω.2 K hK⟩
  have hfixed (ψ : SpatialTest d) : ∀ᵐ ω ∂μ,
      (∑ j, ∫ x, F j (translate x ω) * (coordinateDerivative j ψ x : ℂ)) +
        (∫ x, h (translate x ω) * (ψ x : ℂ)) = 0 := by
    filter_upwards [ae_complex_spatial_divergence_fixedTest μ hμ F h hFm hhm hF hh hw
      ψ ψ.contDiff ψ.hasCompactSupport, hloc] with ω he hl
    rw [integral_finset_sum _ (fun j _ => integrable_spatial_mul_test (hl.1 j)
      (MassiveSpatial.derivative_continuous j ψ)
      (ψ.hasCompactSupport.fderiv_apply ℝ (unitVector j)))] at he
    linear_combination he
  filter_upwards [MassiveSpatial.ae_allTests_of_fixedTest μ
    (fun ω j x => F j (translate x ω)) (fun ω x => h (translate x ω)) hlocal hfixed,
    hloc] with ω he hl
  intro φ hφ hφc
  let ψ : SpatialTest d := ⟨φ, hφ, hφc, Set.subset_univ _⟩
  have ht := he ψ
  have hint (j : Fin d) : Integrable
      (fun x => F j (translate x ω) * (coordinateDerivative j φ x : ℂ)) volume :=
    integrable_spatial_mul_test (hl.1 j)
      ((hφ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hφc.fderiv_apply ℝ (unitVector j))
  rw [integral_finset_sum _ (fun j _ => hint j)]
  exact eq_neg_iff_add_eq_zero.mpr (by simpa only [add_comm] using! ht)


private instance reducedProbability {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) : IsProbabilityMeasure (reducedLaw Q) :=
  reducedLaw_probability Q

/-- Every actual unforced generator pair satisfies its spatial elliptic equation
on one event for all compact smooth tests. -/
theorem IsComplexGeneratorPair.unforced_spatial_allTests
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g)
    {G : Fin d → Lp ℂ 2 (reducedLaw Q)}
    (hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f G) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, g (translate x ω) * (φ x : ℂ)) =
        -(1 / 2 : ℂ) * (∫ x, ∑ j,
          (∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) *
            (coordinateDerivative j φ x : ℂ)) := by
  let F : Fin d → FieldPair d → ℂ := fun j ω => ∑ k, (ω.1 0 j k : ℂ) * G k ω
  have hFm (j : Fin d) : Measurable (F j) :=
    Finset.measurable_sum _ fun k _ =>
      (Complex.continuous_ofReal.comp
        (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable.mul
          (Lp.stronglyMeasurable _).measurable
  have hw (v : Lp ℂ 2 (reducedLaw Q)) (V : Fin d → Lp ℂ 2 (reducedLaw Q))
      (hV : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v V) :
      (∫ ω, ∑ j, F j ω * V j ω ∂reducedLaw Q) =
        -(∫ ω, (2 : ℂ) * g ω * v ω ∂reducedLaw Q) := by
    simpa only [mul_zero, zero_mul, sub_zero] using! hfg.horizontal_flux hG v V hV
  filter_upwards [ae_complex_spatial_divergence_allTests (reducedLaw Q)
    (reducedLaw_stationary Q) F (fun ω => (2 : ℂ) * g ω) hFm
    (measurable_const.mul (Lp.stronglyMeasurable g).measurable)
    (memLp_complex_coefficient_flux Q G) ((Lp.memLp g).const_mul 2) hw] with ω he
  intro φ hφ hφc
  have ht := he φ hφ hφc
  rw [show (fun x => (2 : ℂ) * g (translate x ω) * (φ x : ℂ)) =
    (fun x => (2 : ℂ) * (g (translate x ω) * (φ x : ℂ))) by funext x; ring,
    integral_const_mul] at ht
  simp only [F, translate_matrix, add_zero] at ht
  linear_combination (1 / 2 : ℂ) * ht

/-- The actual resolvent equation, with the literal mass and source and no
generator-graph or gradient premise, holds for all tests on a common event. -/
theorem unforcedComplexResolvent_spatial_allTests
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (s : ℝ) (hs : 0 < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (s : ℂ) * (∫ x, unforcedComplexResolvent Q i s hs rhs (translate x ω) * (φ x : ℂ)) +
        (1 / 2 : ℂ) * (∫ x, ∑ j,
          (∑ k, (ω.1 x j k : ℂ) *
            unforcedComplexResolventGradient Q i s hs rhs k (translate x ω)) *
              (coordinateDerivative j φ x : ℂ)) =
        (∫ x, rhs (translate x ω) * (φ x : ℂ)) := by
  let f := unforcedComplexResolvent Q i s hs rhs
  let g := (s : ℂ) • f - rhs
  have hr : (g : FieldPair d → ℂ) =ᵐ[reducedLaw Q]
      fun ω => (s : ℂ) * f ω - rhs ω := by
    filter_upwards [Lp.coeFn_sub ((s : ℂ) • f) rhs, Lp.coeFn_smul (s : ℂ) f]
      with ω ha hb
    simp only [g, ha, hb, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  filter_upwards [(unforcedComplexResolvent_spec Q i s hs rhs).unforced_spatial_allTests
      (hasComplexHorizontalGradient_unforcedComplexResolvent Q i s hs rhs),
    ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
      (Lp.stronglyMeasurable g).measurable
      ((measurable_const.mul (Lp.stronglyMeasurable f).measurable).sub
        (Lp.stronglyMeasurable rhs).measurable) hr,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) f,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) rhs]
      with ω he hr hf hb
  intro φ hφ hφc
  have ht := he φ hφ hφc
  have hrep : (fun x => g (translate x ω) * (φ x : ℂ)) =ᵐ[volume]
      fun x => (s : ℂ) * (f (translate x ω) * (φ x : ℂ)) -
        rhs (translate x ω) * (φ x : ℂ) := by
    filter_upwards [hr] with x hx
    simp only [hx, Pi.mul_apply, Pi.sub_apply]
    ring
  rw [integral_congr_ae hrep,
    integral_sub ((integrable_spatial_mul_test hf hφ.continuous hφc).const_mul _)
      (integrable_spatial_mul_test hb hφ.continuous hφc), integral_const_mul] at ht
  linear_combination ht


/-- Spatial massive elliptic realization of the literal resolvent. This records
the real and imaginary weak gradients, local L2 value/source/coefficient/flux,
Euclidean gradient energy, and the equation with ALL compact smooth tests. -/
def IsMassiveSpatialRealization {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s)
    (rhs : Lp ℂ 2 (reducedLaw Q)) (ω : FieldPair d) : Prop :=
  let u := fun x => unforcedComplexResolvent Q i s hs rhs (translate x ω)
  let G := fun j x => unforcedComplexResolventGradient Q i s hs rhs j (translate x ω)
  HasWeakGradient Set.univ (fun x => (u x).re) (fun x j => (G j x).re) ∧
  HasWeakGradient Set.univ (fun x => (u x).im) (fun x j => (G j x).im) ∧
  (∀ K : Set (Vec d), IsCompact K →
    MemLp u 2 (volume.restrict K) ∧
    MemLp (fun x => rhs (translate x ω)) 2 (volume.restrict K) ∧
    (∀ j, MemLp (G j) 2 (volume.restrict K)) ∧
    (∀ j k, MemLp (fun x => (ω.1 x j k : ℂ)) 2 (volume.restrict K)) ∧
    (∀ j, MemLp (fun x => ∑ k, (ω.1 x j k : ℂ) * G k x) 2 (volume.restrict K)) ∧
    IntegrableOn (fun x => ∑ j, ‖G j x‖ ^ 2) K volume) ∧
  (∀ φ : Vec d → ℝ, ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
    (s : ℂ) * (∫ x, u x * (φ x : ℂ)) +
      (1 / 2 : ℂ) * (∫ x, ∑ j, (∑ k, (ω.1 x j k : ℂ) * G k x) *
        (coordinateDerivative j φ x : ℂ)) =
      (∫ x, rhs (translate x ω) * (φ x : ℂ)))

/-- Every genuine positive-mass resolvent has its full spatial realization;
all graph, gradient and local-integrability hypotheses are discharged. -/
theorem ae_unforcedComplexResolvent_spatial_realization
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (rhs : Lp ℂ 2 (reducedLaw Q)) :
    ∀ᵐ ω ∂reducedLaw Q, IsMassiveSpatialRealization Q i s hs rhs ω := by
  let G := unforcedComplexResolventGradient Q i s hs rhs
  have hG := hasComplexHorizontalGradient_unforcedComplexResolvent Q i s hs rhs
  have hcoeff (j k : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => (ω.1 x j k : ℂ)) 2 (volume.restrict K) := by
    have hm : Measurable (fun ω : FieldPair d => (ω.1 0 j k : ℂ)) :=
      (Complex.continuous_ofReal.comp
        (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable
    simpa only [translate_matrix, add_zero] using!
      ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
        hm ((memLp_reduced_coefficient_complex Q j k).mono_exponent le_top)
  have hflux (j : Fin d) : ∀ᵐ ω ∂reducedLaw Q,
      ∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => ∑ k, (ω.1 x j k : ℂ) * G k (translate x ω)) 2 (volume.restrict K) := by
    have hm : Measurable (fun ω : FieldPair d => ∑ k, (ω.1 0 j k : ℂ) * G k ω) :=
      Finset.measurable_sum _ fun k _ =>
        (Complex.continuous_ofReal.comp
          (((continuous_eval_const (0 : Vec d)).comp continuous_fst).matrix_elem j k)).measurable.mul
            (Lp.stronglyMeasurable _).measurable
    simpa only [translate_matrix, add_zero] using!
      ae_complex_function_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q)
        hm (memLp_complex_coefficient_flux Q G j)
  filter_upwards [hG.ae_reduced_spatial Q, hG.ae_spatial_gradient_energy,
    ae_complex_orbit_memLp_on_all_compacts (reducedLaw Q) (reducedLaw_stationary Q) rhs,
    ae_all_iff.mpr (fun j => ae_all_iff.mpr (hcoeff j)), ae_all_iff.mpr hflux,
    unforcedComplexResolvent_spatial_allTests Q i s hs rhs] with ω hh he hb hc hF hw
  exact ⟨hh.1, hh.2.1, fun K hK =>
    ⟨(hh.2.2 K hK).1, hb K hK, (hh.2.2 K hK).2,
      fun j k => hc j k K hK, fun j => hF j K hK, he K hK⟩, hw⟩

/-- A prescribed countable mass family has a single full-measure spatial
realization event, with all tests and compact sets inside that event. -/
theorem ae_unforcedComplexResolvent_spatial_realization_countable
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (rhs : Lp ℂ 2 (reducedLaw Q))
    {A : Type*} [Countable A] (s : A → ℝ) (hs : ∀ a, 0 < s a) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ a, IsMassiveSpatialRealization Q i (s a) (hs a) rhs ω :=
  ae_all_iff.mpr fun a => ae_unforcedComplexResolvent_spatial_realization Q i (s a) (hs a) rhs

private theorem memLp_canonicalReducedDrift {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (j : Fin d) :
    MemLp (fun ω => (((1 / 2 : ℝ) * DriftH5.cdiv j ω : ℝ) : ℂ)) 2 (reducedLaw Q) := by
  have hm : Measurable (fun ω => (DriftH5.cdiv j ω : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp (measurable_cdiv j)
  have hb : MemLp (fun ω => (DriftH5.cdiv j ω : ℂ)) 2 (reducedLaw Q) := by
    apply MemLp.of_bound hm.aestronglyMeasurable
      ((d : ℝ) * reducedLipschitzConstant Λ₀)
    simpa only [Complex.norm_real, Real.norm_eq_abs] using! ae_abs_cdiv_le_reduced Q j
  simpa only [Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat] using! hb.const_mul (1 / 2 : ℂ)

/-- The canonical reduced drift is the literal half column divergence in L2. -/
def canonicalReducedDrift {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (j : Fin d) : Lp ℂ 2 (reducedLaw Q) :=
  (memLp_canonicalReducedDrift Q j).toLp _

/-- The constructed drift discharges the frozen observation predicate. -/
theorem isReducedDriftObservation_canonicalReducedDrift
    {d : ℕ} {D : StructuralData d}
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q) :
    IsReducedDriftObservation Q hQ (canonicalReducedDrift Q) := by
  intro j
  exact (memLp_canonicalReducedDrift Q j).coeFn_toLp

/-- The actual massive corrector driven by the actual canonical reduced drift
is a local H1 spatial elliptic solution on one event for every coordinate. -/
theorem ae_massiveCorrector_spatial_realization
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (s : ℝ) (hs : 0 < s) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ j,
      IsMassiveSpatialRealization Q i s hs (canonicalReducedDrift Q j) ω :=
  ae_all_iff.mpr fun j =>
    ae_unforcedComplexResolvent_spatial_realization Q i s hs (canonicalReducedDrift Q j)

/-- All massive corrector coordinates and a prescribed countable mass family
share one full-measure spatial realization event. -/
theorem ae_massiveCorrector_spatial_realization_countable
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) {A : Type*} [Countable A] (s : A → ℝ) (hs : ∀ a, 0 < s a) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ a j,
      IsMassiveSpatialRealization Q i (s a) (hs a) (canonicalReducedDrift Q j) ω :=
  ae_all_iff.mpr fun a => ae_massiveCorrector_spatial_realization Q i (s a) (hs a)


/-- The canonical L2 source is the classical half column divergence at x,
along almost every spatial orbit, with one event for every coordinate. -/
theorem ae_canonicalReducedDrift_spatial {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ j, ∀ᵐ x ∂(volume : Measure (Vec d)),
      canonicalReducedDrift Q j (translate x ω) =
        (((1 / 2 : ℝ) * ∑ k, coordinateDerivative k (fun y => ω.1 y k j) x : ℝ) : ℂ) := by
  apply ae_all_iff.mpr
  intro j
  have hm : Measurable (fun ω => (((1 / 2 : ℝ) * DriftH5.cdiv j ω : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.measurable.comp
      (measurable_const.mul (measurable_cdiv j))
  filter_upwards [ae_complex_spatial_orbit_congr (reducedLaw Q) (reducedLaw_stationary Q)
    (Lp.stronglyMeasurable (canonicalReducedDrift Q j)).measurable hm
    (memLp_canonicalReducedDrift Q j).coeFn_toLp] with ω hω
  filter_upwards [hω] with x hx
  rw [hx]
  congr 2
  unfold DriftH5.cdiv
  apply Finset.sum_congr rfl
  intro k _
  have ht := fderiv_comp_add_left (𝕜 := ℝ) (f := fun y : Vec d => ω.1 y k j)
    (x := (0 : Vec d)) x
  rw [add_zero] at ht
  exact congrArg (fun L : Vec d →L[ℝ] ℝ => L (unitVector k)) ht

/-- The massive corrector's all-test PDE has the classical drift source at x,
with the original anisotropic coefficient, the mass s, and the factor 1/2. -/
theorem ae_massiveCorrector_spatial_equation {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (s : ℝ) (hs : 0 < s) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ j, ∀ φ : Vec d → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (s : ℂ) * (∫ x, unforcedComplexResolvent Q i s hs
        (canonicalReducedDrift Q j) (translate x ω) * (φ x : ℂ)) +
      (1 / 2 : ℂ) * (∫ x, ∑ a, (∑ b, (ω.1 x a b : ℂ) *
        unforcedComplexResolventGradient Q i s hs
          (canonicalReducedDrift Q j) b (translate x ω)) *
            (coordinateDerivative a φ x : ℂ)) =
      (∫ x, ((((1 / 2 : ℝ) * ∑ k,
        coordinateDerivative k (fun y => ω.1 y k j) x : ℝ) : ℂ)) * (φ x : ℂ)) := by
  filter_upwards [ae_all_iff.mpr (fun j =>
    unforcedComplexResolvent_spatial_allTests Q i s hs (canonicalReducedDrift Q j)),
    ae_canonicalReducedDrift_spatial Q] with ω he hb
  intro j φ hφ hφc
  exact (he j φ hφ hφc).trans (integral_congr_ae
    ((hb j).mono fun x hx => congrArg (· * (φ x : ℂ)) hx))


/-- One event for countably many masses contains the all-test weak equations,
local H1 realization, and the classical spatial source with local L2 control. -/
theorem ae_massiveCorrector_classical_realization_countable
    {d : ℕ} [Fact (2 ≤ d)] {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) {A : Type*} [Countable A] (s : A → ℝ) (hs : ∀ a, 0 < s a) :
    ∀ᵐ ω ∂reducedLaw Q, ∀ a j,
      IsMassiveSpatialRealization Q i (s a) (hs a) (canonicalReducedDrift Q j) ω ∧
      (∀ᵐ x ∂(volume : Measure (Vec d)), canonicalReducedDrift Q j (translate x ω) =
        (((1 / 2 : ℝ) * ∑ k, coordinateDerivative k (fun y => ω.1 y k j) x : ℝ) : ℂ)) ∧
      (∀ K : Set (Vec d), IsCompact K →
        MemLp (fun x => (((1 / 2 : ℝ) * ∑ k,
          coordinateDerivative k (fun y => ω.1 y k j) x : ℝ) : ℂ))
            2 (volume.restrict K)) := by
  filter_upwards [ae_massiveCorrector_spatial_realization_countable Q i s hs,
    ae_canonicalReducedDrift_spatial Q] with ω hω hb
  intro a j
  refine ⟨hω a j, hb j, fun K hK => ?_⟩
  exact ((hω a j).2.2.1 K hK).2.1.ae_eq
    ((hb j).filter_mono (ae_mono Measure.restrict_le_self))

end EinsteinFull
