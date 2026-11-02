import EinsteinRelation.Correctors.StationaryCurlRealizationSupport
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# A common event for spatial divergence tests

Source: `paper/main.tex:693-702`. Local L² and separability of the finite
product of scalar spatial L² spaces give a simultaneous test event.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors.SpatialDivergenceGeneral

open StationarySpatialRealization StationaryCurlRealization

variable {d : ℕ}

private theorem derivative_smooth {ψ : Vec d → ℝ}
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (j : Fin d) :
    ContDiff ℝ (⊤ : ℕ∞) (coordinateDerivative j ψ) :=
  ((contDiff_infty_iff_fderiv.mp hψ).2).clm_apply contDiff_const

private theorem derivative_compact {ψ : Vec d → ℝ}
    (hψ : HasCompactSupport ψ) (j : Fin d) :
    HasCompactSupport (coordinateDerivative j ψ) := hψ.fderiv_apply ℝ (unitVector j)

private def testGradient (ψ : SpatialTest d) : Fin d → Lp ℝ 2 (volume : Measure (Vec d)) :=
  fun j => ((derivative_smooth ψ.contDiff j).continuous.memLp_of_hasCompactSupport
    (derivative_compact ψ.hasCompactSupport j)).toLp (coordinateDerivative j ψ)

private def gradientRange (n : ℕ) : Set (Fin d → Lp ℝ 2 (volume : Measure (Vec d))) :=
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

private theorem localComponent_memLp (F : Vec d → Vec d) (n : ℕ)
    (hω : MemLp F 2
      (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)))) (j : Fin d) :
    MemLp ((Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)).indicator
      (fun x => F x j)) 2 volume := by
  rw [memLp_indicator_iff_restrict (isCompact_closedBall (0 : Vec d) _).measurableSet]
  exact (ContinuousLinearMap.proj j : Vec d →L[ℝ] ℝ).comp_memLp' hω

private def localComponent (F : Vec d → Vec d) (n : ℕ)
    (hω : MemLp F 2
      (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)))) (j : Fin d) :
    Lp ℝ 2 (volume : Measure (Vec d)) :=
  (localComponent_memLp F n hω j).toLp _

private def pairing (F : Vec d → Vec d) (n : ℕ)
    (hω : MemLp F 2
      (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)))) :
    (Fin d → Lp ℝ 2 (volume : Measure (Vec d))) →L[ℝ] ℝ :=
  ∑ j : Fin d, (innerSL ℝ (localComponent F n hω j)).comp (ContinuousLinearMap.proj j)

private theorem pairing_test (F : Vec d → Vec d) (n : ℕ)
    (hω : MemLp F 2
      (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1))))
    (ψ : SpatialTest d) (hsupp : tsupport (ψ : Vec d → ℝ) ⊆
      Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)) :
    pairing F n hω (testGradient ψ) =
      ∫ x : Vec d, ∑ j : Fin d,
        coordinateDerivative j ψ x * F x j ∂volume := by
  let K := Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)
  have hp (j : Fin d) :
      (fun x => (localComponent F n hω j) x * (testGradient ψ j) x) =ᵐ[volume]
        fun x => coordinateDerivative j ψ x * F x j := by
    have hl : localComponent F n hω j =ᵐ[volume]
        K.indicator (fun x => F x j) :=
      (localComponent_memLp F n hω j).coeFn_toLp
    have ht : testGradient ψ j =ᵐ[volume] coordinateDerivative j ψ :=
      ((derivative_smooth ψ.contDiff j).continuous.memLp_of_hasCompactSupport
        (derivative_compact ψ.hasCompactSupport j)).coeFn_toLp
    filter_upwards [hl, ht] with x hxl hxt
    rw [hxl, hxt]
    by_cases hx : x ∈ K
    · simp only [Set.indicator_of_mem hx, mul_comm]
    · have hxψ : x ∉ tsupport (ψ : Vec d → ℝ) := fun h => hx (hsupp h)
      have hz : coordinateDerivative j ψ x = 0 := by
        simp only [coordinateDerivative, fderiv_of_notMem_tsupport ℝ hxψ,
          ContinuousLinearMap.zero_apply]
      simp [Set.indicator_of_notMem hx, hz]
  have hi (j : Fin d) : Integrable
      (fun x => coordinateDerivative j ψ x * F x j) volume :=
    ((Lp.memLp (localComponent F n hω j)).integrable_mul
      (Lp.memLp (testGradient ψ j))).congr (hp j)
  simp only [pairing, ContinuousLinearMap.sum_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, innerSL_apply_apply, L2.inner_def,
    RCLike.inner_apply, conj_trivial]
  rw [integral_finset_sum _ fun j _ => hi j]
  apply Finset.sum_congr rfl
  intro j _
  apply integral_congr_ae
  filter_upwards [hp j] with x hx
  simpa only [mul_comm] using hx

/-- Local square integrability supplies one event for all smooth divergence tests. -/
theorem ae_allTests_of_ae_fixedTest {A : Type*} [MeasurableSpace A]
    (μ : Measure A) (F : A → Vec d → Vec d)
    (hloc : ∀ᵐ a ∂μ, ∀ K : Set (Vec d), IsCompact K → MemLp (F a) 2 (volume.restrict K))
    (hfixed : ∀ ψ : SpatialTest d, ∀ᵐ a ∂μ,
      (∫ x : Vec d, ∑ j : Fin d, coordinateDerivative j ψ x * F a x j ∂volume) = 0) :
    ∀ᵐ a ∂μ, ∀ ψ : SpatialTest d,
      (∫ x : Vec d, ∑ j : Fin d, coordinateDerivative j ψ x * F a x j ∂volume) = 0 := by
  have hdense : ∀ᵐ ω ∂μ, ∀ n : ℕ, ∀ p : denseSet (d := d) n,
      (∫ x : Vec d, ∑ j : Fin d,
        coordinateDerivative j (denseTest n p) x * F ω x j ∂volume) = 0 := by
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
  let T : gradientRange (d := d) n → ℝ := fun p => pairing (F ω) n (hω n) p.1
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

end EinsteinRelation.Correctors.SpatialDivergenceGeneral
