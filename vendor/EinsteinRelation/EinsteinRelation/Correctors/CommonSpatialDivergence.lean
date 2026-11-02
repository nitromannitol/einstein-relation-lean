import EinsteinRelation.Correctors.StationaryCurlRealizationSupport
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# A common spatial divergence event

Source: `paper/main.tex:693-698`. For a stationary L² field, vanishing
of the divergence pairing for each fixed smooth test implies simultaneous
vanishing for all tests on one event of full probability. The proof uses
separability of finite products of scalar spatial L² spaces.
-/

open MeasureTheory

noncomputable section

namespace EinsteinRelation.Correctors.SpatialDivergence

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

private theorem localComponent_memLp {Q : Measure (FieldPair d)}
    (W : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) (ω : FieldPair d) (n : ℕ)
    (hω : MemLp (fun x : Vec d => W (translate x ω)) 2
      (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)))) (j : Fin d) :
    MemLp ((Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)).indicator
      (fun x => W (translate x ω) j)) 2 volume := by
  rw [memLp_indicator_iff_restrict (isCompact_closedBall (0 : Vec d) _).measurableSet]
  exact (PiLp.proj (p := 2) (𝕜 := ℝ) (β := fun _ : Fin d => ℝ) j).comp_memLp' hω

private def localComponent {Q : Measure (FieldPair d)}
    (W : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) (ω : FieldPair d) (n : ℕ)
    (hω : MemLp (fun x : Vec d => W (translate x ω)) 2
      (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)))) (j : Fin d) :
    Lp ℝ 2 (volume : Measure (Vec d)) :=
  (localComponent_memLp W ω n hω j).toLp _

private def pairing {Q : Measure (FieldPair d)}
    (W : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) (ω : FieldPair d) (n : ℕ)
    (hω : MemLp (fun x : Vec d => W (translate x ω)) 2
      (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)))) :
    (Fin d → Lp ℝ 2 (volume : Measure (Vec d))) →L[ℝ] ℝ :=
  ∑ j : Fin d, (innerSL ℝ (localComponent W ω n hω j)).comp (ContinuousLinearMap.proj j)

private theorem pairing_test {Q : Measure (FieldPair d)}
    (W : Lp (EuclideanSpace ℝ (Fin d)) 2 Q) (ω : FieldPair d) (n : ℕ)
    (hω : MemLp (fun x : Vec d => W (translate x ω)) 2
      (volume.restrict (Metric.closedBall (0 : Vec d) ((n : ℝ) + 1))))
    (ψ : SpatialTest d) (hsupp : tsupport (ψ : Vec d → ℝ) ⊆
      Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)) :
    pairing W ω n hω (testGradient ψ) =
      ∫ x : Vec d, ∑ j : Fin d,
        coordinateDerivative j ψ x * (W (translate x ω)).ofLp j ∂volume := by
  let K := Metric.closedBall (0 : Vec d) ((n : ℝ) + 1)
  have hp (j : Fin d) :
      (fun x => (localComponent W ω n hω j) x * (testGradient ψ j) x) =ᵐ[volume]
        fun x => coordinateDerivative j ψ x * W (translate x ω) j := by
    have hl : localComponent W ω n hω j =ᵐ[volume]
        K.indicator (fun x => W (translate x ω) j) :=
      (localComponent_memLp W ω n hω j).coeFn_toLp
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
      (fun x => coordinateDerivative j ψ x * W (translate x ω) j) volume :=
    ((Lp.memLp (localComponent W ω n hω j)).integrable_mul
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

/-- A stationary square-integrable vector field has a common event for all
smooth compactly supported spatial divergence tests whenever each fixed
test vanishes almost surely. No uncountable intersection is taken. -/
theorem ae_allTests_of_ae_fixedTest
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (W : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hfixed : ∀ ψ : SpatialTest d, ∀ᵐ ω ∂Q,
      (∫ x : Vec d, ∑ j : Fin d,
        coordinateDerivative j ψ x * (W (translate x ω)).ofLp j ∂volume) = 0) :
    ∀ᵐ ω ∂Q, ∀ ψ : SpatialTest d,
      (∫ x : Vec d, ∑ j : Fin d,
        coordinateDerivative j ψ x * (W (translate x ω)).ofLp j ∂volume) = 0 := by
  have hdense : ∀ᵐ ω ∂Q, ∀ n : ℕ, ∀ p : denseSet (d := d) n,
      (∫ x : Vec d, ∑ j : Fin d,
        coordinateDerivative j (denseTest n p) x * (W (translate x ω)).ofLp j ∂volume) = 0 := by
    apply ae_all_iff.mpr
    intro n
    letI : Countable (denseSet (d := d) n) :=
      (Classical.choose_spec (exists_dense_tests n)).1.to_subtype
    exact ae_all_iff.mpr fun p => hfixed (denseTest n p)
  filter_upwards [ae_spatialRealization_locallyL2 hQ W, hdense] with ω hω hD
  intro ψ
  obtain ⟨R, hR⟩ := (Metric.isBounded_iff_subset_closedBall (0 : Vec d)).mp
    ψ.hasCompactSupport.isCompact.isBounded
  obtain ⟨n, hn⟩ := exists_nat_gt R
  have hsupport : tsupport (ψ : Vec d → ℝ) ⊆
      Metric.closedBall (0 : Vec d) ((n : ℝ) + 1) :=
    hR.trans (Metric.closedBall_subset_closedBall (le_trans hn.le (by norm_num)))
  let F : gradientRange (d := d) n → ℝ := fun p => pairing W ω n (hω n) p.1
  have hF : Continuous F := (pairing W ω n (hω n)).continuous.comp continuous_subtype_val
  have hz : IsClosed {p : gradientRange (d := d) n | F p = 0} :=
    isClosed_eq hF continuous_const
  have hsub : denseSet (d := d) n ⊆ {p : gradientRange (d := d) n | F p = 0} := by
    intro p hp
    let q : denseSet (d := d) n := ⟨p, hp⟩
    have hs := denseTest_spec n q
    change pairing W ω n (hω n) p.1 = 0
    rw [← hs.2, pairing_test W ω n (hω n) (denseTest n q) hs.1]
    exact hD n q
  have hcl := closure_minimal hsub hz
  have hd : closure (denseSet (d := d) n) = Set.univ :=
    (Classical.choose_spec (exists_dense_tests n)).2.closure_eq
  rw [hd] at hcl
  have hres := hcl (Set.mem_univ (⟨testGradient ψ, ψ, hsupport, rfl⟩ : gradientRange n))
  change pairing W ω n (hω n) (testGradient ψ) = 0 at hres
  rw [pairing_test W ω n (hω n) ψ hsupport] at hres
  exact hres

end EinsteinRelation.Correctors.SpatialDivergence

