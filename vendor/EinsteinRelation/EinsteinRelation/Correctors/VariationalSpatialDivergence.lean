import EinsteinRelation.Correctors.StationaryCurlFubiniSupport
import EinsteinRelation.Correctors.CanonicalFluxDivergenceSupport
import EinsteinRelation.Entropy.DivergenceSecondAssertion
import EinsteinRelation.Entropy.EllipticRegularity
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport
import Mathlib.MeasureTheory.SpecificCodomains.Pi

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Variational orthogonality gives the actual weak horizontal divergence. -/
theorem hasWeakHorizontalDivergence_zero_of_variational {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (W : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hW : ∀ f : horizontalH1 Q hQ,
      inner ℝ (horizontalEuclideanGradient Q hQ f) W = 0) :
    HasWeakHorizontalDivergence Q hQ (fun ω => (W ω).ofLp) (fun _ => 0) := by
  have hcoord (i : Fin d) : MemLp (fun ω => (W ω).ofLp i) 2 Q :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (Lp.memLp W)
  refine ⟨fun i => (hcoord i).integrable (by norm_num), integrable_zero _ _ _, ?_⟩
  intro F _ DF hDF
  let f : horizontalH1 Q hQ := ⟨F, ⟨DF, hDF⟩⟩
  have hgrad := horizontalH1Gradient_eq_of_hasHorizontalLpDerivative Q hQ f DF hDF
  have hrep : ∀ᵐ ω ∂Q, ∀ i : Fin d,
      (horizontalEuclideanGradient Q hQ f ω).ofLp i = DF i ω := by
    apply ae_all_iff.mpr
    intro i
    simpa only [hgrad] using! horizontalEuclideanGradient_coordinates Q hQ f i
  have h := hW f
  rw [L2.inner_def] at h
  simpa only [zero_mul, integral_zero, neg_zero] using
    (integral_congr_ae (hrep.mono fun ω hω => by
      simp only [PiLp.inner_apply, RCLike.inner_apply, conj_trivial]
      exact Finset.sum_congr rfl fun i _ => by rw [hω i])).symm.trans h

/-- Horizontal variational orthogonality implies the spatial divergence
identity for one fixed test, a transport step for `paper/main.tex:693-698`.
The null set in this lemma may depend on the test. -/
theorem ae_spatial_divergence_fixedTest {d : ℕ} [Fact (2 ≤ d)]
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (W : Lp (EuclideanSpace ℝ (Fin d)) 2 Q)
    (hW : ∀ f : horizontalH1 Q hQ,
      inner ℝ (horizontalEuclideanGradient Q hQ f) W = 0)
    (ψ : Vec d → ℝ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψc : HasCompactSupport ψ) :
    ∀ᵐ ω ∂Q, (∫ x : Vec d,
      ∑ j : Fin d, coordinateDerivative j ψ x * (W (translate x ω)).ofLp j ∂volume) = 0 := by
  have hVm : Measurable (fun ω => (W ω).ofLp) :=
    (PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).measurable.comp
      (Lp.stronglyMeasurable W).measurable
  have hVi (i : Fin d) : Integrable (fun ω => (W ω).ofLp i) Q :=
    ((EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' (Lp.memLp W)).integrable (by norm_num)
  have h := Entropy.ae_horizontalMollify_eq_of_hasWeakHorizontalDivergence hQ
    hψ hψc
    hVm hVi measurable_const (integrable_zero _ _ _)
    (hasWeakHorizontalDivergence_zero_of_variational Q hQ W hW)
  filter_upwards [h, StationarySpatialRealization.ae_spatialRealization_memLp_on_all_compacts hQ W]
    with ω hω hlocal
  have hi (j : Fin d) : Integrable
      (fun x => coordinateDerivative j ψ x * (W (translate x ω)).ofLp j) volume := by
    have hl : LocallyIntegrable (fun x => (W (translate x ω)).ofLp j) volume := by
      rw [locallyIntegrable_iff]
      intro K hK
      letI : IsFiniteMeasure (volume.restrict K) := isFiniteMeasure_restrict.mpr hK.measure_ne_top
      exact ((EuclideanSpace.proj (𝕜 := ℝ) j).comp_memLp' (hlocal K hK)).integrable (by norm_num)
    simpa only [smul_eq_mul, coordinateDerivative] using! hl.integrable_smul_left_of_hasCompactSupport
      ((hψ.continuous_fderiv (by simp)).clm_apply continuous_const)
      (hψc.fderiv_apply ℝ (unitVector j))
  have hk (j : Fin d) : Entropy.divKernel ψ j =
      fun x => -coordinateDerivative j ψ x := by
    funext x
    simp only [Entropy.divKernel,
      Entropy.coordinateDerivative_reflectKernel (hψ.differentiable (by simp)), neg_neg]
  change (∫ x : Vec d, ψ x * (0 : ℝ)) = _ at hω
  simp only [mul_zero, integral_zero] at hω
  simp only [horizontalMollify] at hω
  simp only [hk, neg_mul, integral_neg, Finset.sum_neg_distrib] at hω
  rw [integral_finset_sum _ fun j _ => hi j]
  linarith

end EinsteinRelation.Correctors
