import EinsteinRelation.Correctors.ScalarOrbitPairing
import EinsteinRelation.Calculus.Weak
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# One event for scalar spatial weak derivatives

Source: `paper/main.tex:240-248,693-698`. On each compact support,
the weak derivative pairing is continuous in the scalar spatial L²
classes of a test and its derivative. A countable dense subset therefore
suffices to obtain all smooth tests simultaneously.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors.SpatialScalar

open StationaryCurlRealization

variable {d : ℕ}

private theorem derivative_continuous (i : Fin d) (ψ : SpatialTest d) :
    Continuous (coordinateDerivative i ψ) :=
  (ψ.contDiff.continuous_fderiv (by simp)).clm_apply continuous_const

private def testPair (i : Fin d) (ψ : SpatialTest d) :
    Lp ℝ 2 (volume : Measure (Vec d)) × Lp ℝ 2 (volume : Measure (Vec d)) :=
  (((derivative_continuous i ψ).memLp_of_hasCompactSupport
    (ψ.hasCompactSupport.fderiv_apply ℝ (unitVector i))).toLp _,
    (ψ.contDiff.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport).toLp _)

private def testRange (i : Fin d) (n : ℕ) :
    Set (Lp ℝ 2 (volume : Measure (Vec d)) × Lp ℝ 2 (volume : Measure (Vec d))) :=
  {p | ∃ ψ : SpatialTest d,
    tsupport (ψ : Vec d → ℝ) ⊆ Metric.closedBall 0 ((n : ℝ) + 1) ∧ testPair i ψ = p}

private theorem exists_dense_tests (i : Fin d) (n : ℕ) :
    ∃ D : Set (testRange i n), D.Countable ∧ Dense D := by
  letI : Fact (1 ≤ (2 : ENNReal)) := ⟨by norm_num⟩
  letI : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by simp⟩
  exact TopologicalSpace.exists_countable_dense _

private def denseTests (i : Fin d) (n : ℕ) : Set (testRange i n) :=
  Classical.choose (exists_dense_tests i n)

private def denseTest (i : Fin d) (n : ℕ) (p : denseTests i n) : SpatialTest d :=
  Classical.choose p.1.2

private theorem denseTest_spec (i : Fin d) (n : ℕ) (p : denseTests i n) :
    tsupport (denseTest i n p : Vec d → ℝ) ⊆ Metric.closedBall 0 ((n : ℝ) + 1) ∧
      testPair i (denseTest i n p) = p.1.1 := Classical.choose_spec p.1.2

private def localLp (f : Vec d → ℝ) (n : ℕ)
    (hf : MemLp f 2 (volume.restrict (Metric.closedBall 0 ((n : ℝ) + 1)))) :
    Lp ℝ 2 (volume : Measure (Vec d)) :=
  ((memLp_indicator_iff_restrict (isCompact_closedBall (0 : Vec d) _).measurableSet).mpr hf).toLp _

private def pairing (f g : Vec d → ℝ) (n : ℕ)
    (hf : MemLp f 2 (volume.restrict (Metric.closedBall 0 ((n : ℝ) + 1))))
    (hg : MemLp g 2 (volume.restrict (Metric.closedBall 0 ((n : ℝ) + 1)))) :
    (Lp ℝ 2 (volume : Measure (Vec d)) × Lp ℝ 2 (volume : Measure (Vec d))) →L[ℝ] ℝ :=
  (innerSL ℝ (localLp f n hf)).comp (ContinuousLinearMap.fst ℝ _ _) +
    (innerSL ℝ (localLp g n hg)).comp (ContinuousLinearMap.snd ℝ _ _)

private theorem local_inner_test (f a : Vec d → ℝ) (n : ℕ)
    (hf : MemLp f 2 (volume.restrict (Metric.closedBall 0 ((n : ℝ) + 1))))
    (ha : MemLp a 2 volume)
    (hsupp : ∀ x ∉ Metric.closedBall (0 : Vec d) ((n : ℝ) + 1), a x = 0) :
    inner ℝ (localLp f n hf) (ha.toLp a) = ∫ x, f x * a x := by
  have hl : localLp f n hf =ᵐ[volume]
      (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)).indicator f :=
    ((memLp_indicator_iff_restrict (isCompact_closedBall (0 : Vec d) _).measurableSet).mpr hf).coeFn_toLp
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hl, ha.coeFn_toLp] with x hxl hxa
  rw [hxl, hxa, RCLike.inner_apply, conj_trivial]
  by_cases hx : x ∈ Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)
  · simp only [Set.indicator_of_mem hx, mul_comm]
  · simp only [Set.indicator_of_notMem hx, hsupp x hx, mul_zero]

private theorem pairing_test (f g : Vec d → ℝ) (n : ℕ)
    (hf : MemLp f 2 (volume.restrict (Metric.closedBall 0 ((n : ℝ) + 1))))
    (hg : MemLp g 2 (volume.restrict (Metric.closedBall 0 ((n : ℝ) + 1))))
    (i : Fin d) (ψ : SpatialTest d)
    (hsupp : tsupport (ψ : Vec d → ℝ) ⊆ Metric.closedBall 0 ((n : ℝ) + 1)) :
    pairing f g n hf hg (testPair i ψ) =
      (∫ x, f x * coordinateDerivative i ψ x) + ∫ x, g x * ψ x := by
  change inner ℝ (localLp f n hf) (testPair i ψ).1 +
    inner ℝ (localLp g n hg) (testPair i ψ).2 = _
  congr 1
  · change inner ℝ (localLp f n hf) _ = _
    apply local_inner_test f (coordinateDerivative i ψ) n hf
      ((derivative_continuous i ψ).memLp_of_hasCompactSupport
        (ψ.hasCompactSupport.fderiv_apply ℝ (unitVector i)))
    intro x hx
    simp only [coordinateDerivative,
      fderiv_of_notMem_tsupport ℝ (fun h => hx (hsupp h)), ContinuousLinearMap.zero_apply]
  · change inner ℝ (localLp g n hg) _ = _
    apply local_inner_test g ψ n hg
      (ψ.contDiff.continuous.memLp_of_hasCompactSupport ψ.hasCompactSupport)
    intro x hx
    exact image_eq_zero_of_notMem_tsupport (fun h => hx (hsupp h))

/-- Local L² bounds permit a single full-measure event for every scalar
weak derivative test, with no uncountable intersection of events. -/
theorem ae_allTests_of_ae_fixedTest {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f g : A → Vec d → ℝ) (i : Fin d)
    (hloc : ∀ᵐ ω ∂μ, ∀ K : Set (Vec d), IsCompact K →
      MemLp (f ω) 2 (volume.restrict K) ∧ MemLp (g ω) 2 (volume.restrict K))
    (hfixed : ∀ ψ : SpatialTest d, ∀ᵐ ω ∂μ,
      (∫ x, f ω x * coordinateDerivative i ψ x) = -(∫ x, g ω x * ψ x)) :
    ∀ᵐ ω ∂μ, ∀ ψ : SpatialTest d,
      (∫ x, f ω x * coordinateDerivative i ψ x) = -(∫ x, g ω x * ψ x) := by
  have hdense : ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ p : denseTests i n,
      (∫ x, f ω x * coordinateDerivative i (denseTest i n p) x) =
        -(∫ x, g ω x * denseTest i n p x) := by
    apply ae_all_iff.mpr
    intro n
    letI : Countable (denseTests i n) :=
      (Classical.choose_spec (exists_dense_tests i n)).1.to_subtype
    exact ae_all_iff.mpr fun p => hfixed (denseTest i n p)
  filter_upwards [hloc, hdense] with ω hω hD
  intro ψ
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp
    ψ.hasCompactSupport.isCompact.isBounded
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hsupp : tsupport (ψ : Vec d → ℝ) ⊆ Metric.closedBall 0 ((n : ℝ) + 1) :=
    hR.trans (Metric.closedBall_subset_closedBall (le_trans hn.le (by norm_num)))
  obtain ⟨hf, hg⟩ := hω _ (isCompact_closedBall (0 : Vec d) ((n : ℝ) + 1))
  let F : testRange i n → ℝ := fun p => pairing (f ω) (g ω) n hf hg p.1
  have hF : Continuous F := (pairing (f ω) (g ω) n hf hg).continuous.comp continuous_subtype_val
  have hsub : denseTests i n ⊆ {p : testRange i n | F p = 0} := by
    intro p hp
    let q : denseTests i n := ⟨p, hp⟩
    have hs := denseTest_spec i n q
    change pairing (f ω) (g ω) n hf hg p.1 = 0
    rw [← hs.2, pairing_test (f ω) (g ω) n hf hg i (denseTest i n q) hs.1]
    exact eq_neg_iff_add_eq_zero.mp (hD n q)
  have hcl := closure_minimal hsub (isClosed_eq hF continuous_const)
  have hd : Dense (denseTests i n) :=
    (Classical.choose_spec (exists_dense_tests i n)).2
  rw [hd.closure_eq] at hcl
  have hres := hcl (Set.mem_univ (⟨testPair i ψ, ψ, hsupp, rfl⟩ : testRange i n))
  change pairing (f ω) (g ω) n hf hg (testPair i ψ) = 0 at hres
  rw [pairing_test (f ω) (g ω) n hf hg i ψ hsupp] at hres
  exact eq_neg_iff_add_eq_zero.mpr hres

/-- The simultaneous test identity is a literal samplewise weak derivative. -/
theorem ae_hasWeakPartialDerivative_of_ae_fixedTest {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (f g : A → Vec d → ℝ) (i : Fin d)
    (hloc : ∀ᵐ ω ∂μ, ∀ K : Set (Vec d), IsCompact K →
      MemLp (f ω) 2 (volume.restrict K) ∧ MemLp (g ω) 2 (volume.restrict K))
    (hfixed : ∀ ψ : SpatialTest d, ∀ᵐ ω ∂μ,
      (∫ x, f ω x * coordinateDerivative i ψ x) = -(∫ x, g ω x * ψ x)) :
    ∀ᵐ ω ∂μ, HasWeakPartialDerivative Set.univ i (f ω) (g ω) := by
  filter_upwards [hloc, ae_allTests_of_ae_fixedTest μ f g i hloc hfixed] with ω hω ht
  have hi (h : Vec d → ℝ)
      (hh : ∀ K : Set (Vec d), IsCompact K → MemLp h 2 (volume.restrict K)) :
      LocallyIntegrableOn h Set.univ volume := by
    apply locallyIntegrableOn_univ.mpr
    apply locallyIntegrable_iff.mpr
    intro K hK
    letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
    exact (hh K hK).integrable (by norm_num)
  refine ⟨hi _ (fun K hK => (hω K hK).1), hi _ (fun K hK => (hω K hK).2), ?_⟩
  intro φ hφ
  let ψ : SpatialTest d := ⟨φ, hφ.1, hφ.2.1, Set.subset_univ _⟩
  simpa only [Measure.restrict_univ] using! ht ψ

end EinsteinRelation.Correctors.SpatialScalar
