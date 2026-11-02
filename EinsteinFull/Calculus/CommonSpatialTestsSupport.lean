import EinsteinRelation.Correctors.StationaryCurlRealizationSupport
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# One event for inhomogeneous spatial weak equations

The countable dense-test argument of the pinned blueprint's
`Correctors/CommonSpatialDivergenceGeneral.lean` is extended to the value and
all first derivatives of a test. This retains the nonzero source and arbitrary
complex flux. Local square integrability makes the full pairing continuous.

Reuse attribution: the EinsteinRelation blueprint library.
The helper below is ordinary support, not a replacement numbered statement.
-/

open MeasureTheory

noncomputable section

namespace EinsteinFull.CommonSpatialTests

open EinsteinRelation EinsteinRelation.Correctors
open StationarySpatialRealization StationaryCurlRealization

variable {d : ℕ}

private theorem derivative_smooth {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j ψ) :=
  ((contDiff_infty_iff_fderiv.mp hψ).2).clm_apply contDiff_const

private theorem derivative_compact {ψ : Vec d → ℝ}
    (hψ : HasCompactSupport ψ) (j : Fin d) :
    HasCompactSupport (coordinateDerivative j ψ) := hψ.fderiv_apply ℝ (unitVector j)

private def testValue (ψ : SpatialTest d) : Option (Fin d) → Vec d → ℝ
  | none => ψ
  | some j => coordinateDerivative j ψ

private theorem testValue_continuous (ψ : SpatialTest d) (j : Option (Fin d)) :
    Continuous (testValue ψ j) := by
  cases j with
  | none => exact ψ.contDiff.continuous
  | some j => exact (derivative_smooth ψ.contDiff j).continuous

private theorem testValue_compact (ψ : SpatialTest d) (j : Option (Fin d)) :
    HasCompactSupport (testValue ψ j) := by
  cases j with
  | none => exact ψ.hasCompactSupport
  | some j => exact derivative_compact ψ.hasCompactSupport j

private theorem testValue_eq_zero (ψ : SpatialTest d) (j : Option (Fin d))
    {x : Vec d} (hx : x ∉ tsupport (ψ : Vec d → ℝ)) : testValue ψ j x = 0 := by
  cases j with
  | none => exact image_eq_zero_of_notMem_tsupport hx
  | some j =>
    simp only [testValue, coordinateDerivative, fderiv_of_notMem_tsupport ℝ hx,
      ContinuousLinearMap.zero_apply]

private theorem testValue_memLp (ψ : SpatialTest d) (j : Option (Fin d)) :
    MemLp (fun x => (testValue ψ j x : ℂ)) 2 (volume : Measure (Vec d)) :=
  Complex.ofRealCLM.comp_memLp'
    ((testValue_continuous ψ j).memLp_of_hasCompactSupport (testValue_compact ψ j))

private def testGradient (ψ : SpatialTest d) :
    Option (Fin d) → Lp ℂ 2 (volume : Measure (Vec d)) :=
  fun j => (testValue_memLp ψ j).toLp (fun x => (testValue ψ j x : ℂ))

private def gradientRange (n : ℕ) : Set (Option (Fin d) → Lp ℂ 2 (volume : Measure (Vec d))) :=
  {p | ∃ ψ : SpatialTest d,
    tsupport (ψ : Vec d → ℝ) ⊆ Metric.closedBall (0 : Vec d) ((n : ℝ) + 1) ∧
    testGradient ψ = p}

private theorem exists_dense_tests (n : ℕ) :
    ∃ D : Set (gradientRange (d := d) n), D.Countable ∧ Dense D := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  exact TopologicalSpace.exists_countable_dense _

private def denseSet (n : ℕ) : Set (gradientRange (d := d) n) :=
  Classical.choose (exists_dense_tests n)

private def denseTest (n : ℕ) (p : denseSet (d := d) n) : SpatialTest d :=
  Classical.choose p.1.2

private theorem denseTest_spec (n : ℕ) (p : denseSet (d := d) n) :
    tsupport (denseTest n p : Vec d → ℝ) ⊆
      Metric.closedBall (0 : Vec d) ((n : ℝ) + 1) ∧
    testGradient (denseTest n p) = p.1.1 := Classical.choose_spec p.1.2

private theorem localComponent_memLp (F : Option (Fin d) → Vec d → ℂ) (n : ℕ)
    (hω : ∀ j, MemLp (F j) 2
      (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1))))
    (j : Option (Fin d)) :
    MemLp ((Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)).indicator
      (fun x => star (F j x))) 2 volume := by
  rw [memLp_indicator_iff_restrict (isCompact_closedBall (0 : Vec d) _).measurableSet]
  exact (hω j).star

private def localComponent (F : Option (Fin d) → Vec d → ℂ) (n : ℕ)
    (hω : ∀ j, MemLp (F j) 2
      (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1))))
    (j : Option (Fin d)) : Lp ℂ 2 (volume : Measure (Vec d)) :=
  (localComponent_memLp F n hω j).toLp _

private def pairing (F : Option (Fin d) → Vec d → ℂ) (n : ℕ)
    (hω : ∀ j, MemLp (F j) 2
      (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)))) :
    (Option (Fin d) → Lp ℂ 2 (volume : Measure (Vec d))) →L[ℂ] ℂ :=
  ∑ j : Option (Fin d),
    (innerSL ℂ (localComponent F n hω j)).comp (ContinuousLinearMap.proj j)

private theorem pairing_test (F : Option (Fin d) → Vec d → ℂ) (n : ℕ)
    (hω : ∀ j, MemLp (F j) 2
      (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1))))
    (ψ : SpatialTest d) (hsupp : tsupport (ψ : Vec d → ℝ) ⊆
      Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)) :
    pairing F n hω (testGradient ψ) =
      ∫ x : Vec d, ∑ j : Option (Fin d), F j x * (testValue ψ j x : ℂ) := by
  let K := Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)
  have hp (j : Option (Fin d)) :
      (fun x => (testGradient ψ j) x * star ((localComponent F n hω j) x)) =ᵐ[volume]
        fun x => F j x * (testValue ψ j x : ℂ) := by
    have hl : localComponent F n hω j =ᵐ[volume]
        K.indicator (fun x => star (F j x)) :=
      (localComponent_memLp F n hω j).coeFn_toLp
    have ht : testGradient ψ j =ᵐ[volume] fun x => (testValue ψ j x : ℂ) :=
      (testValue_memLp ψ j).coeFn_toLp
    filter_upwards [hl, ht] with x hxl hxt
    rw [hxl, hxt]
    by_cases hx : x ∈ K
    · simp only [Set.indicator_of_mem hx, star_star, mul_comm]
    · have hz := testValue_eq_zero ψ j (fun h => hx (hsupp h))
      simp only [Set.indicator_of_notMem hx, hz, Complex.ofReal_zero, mul_zero,
        star_zero]
  have hi (j : Option (Fin d)) : Integrable
      (fun x => F j x * (testValue ψ j x : ℂ)) volume :=
    ((Lp.memLp (testGradient ψ j)).integrable_mul
      (Lp.memLp (localComponent F n hω j)).star).congr (hp j)
  simp only [pairing, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, innerSL_apply_apply, L2.inner_def,
    RCLike.inner_apply]
  rw [integral_finset_sum _ fun j _ => hi j]
  apply Finset.sum_congr rfl
  intro j _
  exact integral_congr_ae (hp j)

/-- Local square integrability supplies one event for all smooth divergence tests. -/
private theorem ae_allTests_of_ae_fixedTest {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (F : A → Option (Fin d) → Vec d → ℂ)
    (hloc : ∀ᵐ a ∂μ, ∀ K : Set (Vec d), IsCompact K → ∀ j, MemLp (F a j) 2 (volume.restrict K))
    (hfixed : ∀ ψ : SpatialTest d, ∀ᵐ a ∂μ,
      (∫ x : Vec d, ∑ j : Option (Fin d), F a j x * (testValue ψ j x : ℂ) ∂volume) = 0) :
    ∀ᵐ a ∂μ, ∀ ψ : SpatialTest d,
      (∫ x : Vec d, ∑ j : Option (Fin d), F a j x * (testValue ψ j x : ℂ) ∂volume) = 0 := by
  have hdense : ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ p : denseSet (d := d) n,
      (∫ x : Vec d, ∑ j : Option (Fin d),
        F ω j x * (testValue (denseTest n p) j x : ℂ) ∂volume) = 0 := by
    apply ae_all_iff.mpr
    intro n
    letI : Countable (denseSet (d := d) n) :=
      (Classical.choose_spec (exists_dense_tests n)).1.to_subtype
    exact ae_all_iff.mpr fun p => hfixed (denseTest n p)
  filter_upwards [hloc, hdense] with ω hlocω hD
  have hω (n : ℕ) := hlocω _ (isCompact_closedBall (0 : Vec d) ((n : ℝ) + 1))
  intro ψ
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp
    ψ.hasCompactSupport.isCompact.isBounded
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hsupport : tsupport (ψ : Vec d → ℝ) ⊆
      Metric.closedBall (0 : Vec d) ((n : ℝ) + 1) :=
    hR.trans (Metric.closedBall_subset_closedBall (le_trans hn.le (by norm_num)))
  let T : gradientRange (d := d) n → ℂ := fun p => pairing (F ω) n (hω n) p.1
  have hF : Continuous T := (pairing (F ω) n (hω n)).continuous.comp continuous_subtype_val
  have hz : IsClosed {p : gradientRange (d := d) n | T p = 0} :=
    isClosed_eq hF continuous_const
  have hsub : denseSet (d := d) n ⊆ {p : gradientRange (d := d) n | T p = 0} := by
    intro p hp
    let q : denseSet (d := d) n := ⟨p, hp⟩
    have hs := denseTest_spec n q
    change pairing (F ω) n (hω n) p.1 = 0
    rw [← hs.2, pairing_test (F ω) n (hω n) (denseTest n q) hs.1]
    exact hD n q
  have hcl := closure_minimal hsub hz
  have hd : closure (denseSet (d := d) n) = Set.univ :=
    (Classical.choose_spec (exists_dense_tests n)).2.closure_eq
  rw [hd] at hcl
  have hres := hcl (Set.mem_univ (⟨testGradient ψ, ψ, hsupport, rfl⟩ : gradientRange n))
  change pairing (F ω) n (hω n) (testGradient ψ) = 0 at hres
  rw [pairing_test (F ω) n (hω n) ψ hsupport] at hres
  exact hres

end EinsteinFull.CommonSpatialTests

namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Correctors.StationaryCurlRealization

/-- Local square integrability of both source and flux gives one environment
event for every smooth compact spatial test of an inhomogeneous equation. -/
theorem ae_all_spatial_tests_of_ae_fixed_test {d : ℕ} {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (h : A → Vec d → ℂ) (F : A → Fin d → Vec d → ℂ)
    (hloc : ∀ᵐ a ∂μ, ∀ K : Set (Vec d), IsCompact K →
      MemLp (h a) 2 (volume.restrict K) ∧ ∀ j, MemLp (F a j) 2 (volume.restrict K))
    (hfixed : ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      ∀ᵐ a ∂μ, (∫ x, h a x * (φ x : ℂ) +
        ∑ j, F a j x * (coordinateDerivative j φ x : ℂ)) = 0) :
    ∀ᵐ a ∂μ, ∀ (φ : Vec d → ℝ), ContDiff ℝ (⊤ : ℕ∞) φ → HasCompactSupport φ →
      (∫ x, h a x * (φ x : ℂ) +
        ∑ j, F a j x * (coordinateDerivative j φ x : ℂ)) = 0 := by
  let C (a : A) : Option (Fin d) → Vec d → ℂ := fun j => j.elim (h a) (F a)
  have hC : ∀ᵐ a ∂μ, ∀ K : Set (Vec d), IsCompact K →
      ∀ j, MemLp (C a j) 2 (volume.restrict K) := by
    filter_upwards [hloc] with a ha
    intro K hK j
    cases j with
    | none => exact (ha K hK).1
    | some j => exact (ha K hK).2 j
  have he := CommonSpatialTests.ae_allTests_of_ae_fixedTest μ C hC (fun ψ => by
    simpa only [Fintype.sum_option, C, Option.elim_none, Option.elim_some,
      CommonSpatialTests.testValue] using hfixed ψ ψ.contDiff ψ.hasCompactSupport)
  filter_upwards [he] with a ha
  intro φ hφ hφc
  let ψ : SpatialTest d := ⟨φ, hφ, hφc, Set.subset_univ _⟩
  simpa only [Fintype.sum_option, C, Option.elim_none, Option.elim_some,
    CommonSpatialTests.testValue] using! ha ψ

end EinsteinFull
