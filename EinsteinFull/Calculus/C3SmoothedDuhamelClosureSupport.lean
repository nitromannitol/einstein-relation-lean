import EinsteinFull.Calculus.C4SmoothedDuhamelSupport
import EinsteinFull.Work.W4.HomogeneousTimeHorizontalGeneratorSupport
import EinsteinFull.Work.W4.HomogeneousAllDataHorizontalSmoothingSupport
import EinsteinFull.Calculus.ComplexHorizontalMeanSupport
import EinsteinFull.Calculus.ComplexLpSupport
import EinsteinFull.Calculus.ComplexTransposeSupport
import EinsteinFull.Work.W3.GaussianDerivativeAveragingSupport
import EinsteinFull.Work.W3.HomogeneousGaussianH1LegSupport
import EinsteinFull.Calculus.S3TranslationAverage
import EinsteinFull.Calculus.ScalarWeightSupport
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import EinsteinFull.Blueprint.Roots.node_p_u3A_scalar
import EinsteinFull.Blueprint.Roots.node_l_u3A_forced_u2D_flux
import Mathlib.Analysis.Calculus.FDeriv.Measurable

/-! Cancellation of the homogeneous action in the actual centered endpoint equation.
This is internal support for paper/main.tex:1140–1148, not the late-time estimate. -/

open MeasureTheory
open scoped NNReal Topology
noncomputable section
namespace EinsteinFull
open EinsteinRelation
attribute [local instance] reducedLaw_probability

/-- The literal time-derivative kernel is a bounded operator on actual L2 data. -/
def c3GaussianTimeDerivativeCLM {d : ℕ} {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (i : Fin d) (s : ℝ) (hs : 0 < s) (ζ : ℂ) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x : Vec d, homogenizedGaussianKernelTimeDerivative Q i s hs ζ x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f
      map_add' := fun f g => by
        simp only [map_add, smul_add]
        exact integral_add (integrable_homogeneousAverageTimeDerivative_integrand Q i s hs ζ f)
          (integrable_homogeneousAverageTimeDerivative_integrand Q i s hs ζ g)
      map_smul' := fun c f => by
        simp only [map_smul, RingHom.id_apply, smul_comm _ c, integral_smul] }
    (∫ x : Vec d, ‖homogenizedGaussianKernelTimeDerivative Q i s hs ζ x‖)
    (fun f => by
      calc
        _ ≤ ∫ x : Vec d, ‖homogenizedGaussianKernelTimeDerivative Q i s hs ζ x •
            complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f‖ :=
          norm_integral_le_integral_norm _
        _ = _ := by
          simp_rw [norm_smul, norm_complexTranslation]
          rw [integral_mul_const])

/-- Weak testing of the opposite-force time derivative for every actual L2
backward datum. Density is used only for the test, not for the physical endpoint. -/
theorem c3GaussianTimeDerivative_negativeForce_weak {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (s : ℝ) (hs : 0 < s) (ξ : ℂ)
    (u : Lp ℂ 2 (reducedLaw Q)) (G : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hu : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) u G)
    (g : Lp ℂ 2 (reducedLaw Q)) :
    c4EndpointPairing Q u (homogeneousGaussianEvolutionTimeDerivative Q i (-ξ) g s) =
      -(1 / 2 : ℂ) * ∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
        c4EndpointPairing Q (G j) (homogeneousGaussianHorizontalGradient Q i s hs (-ξ) g k) -
      ξ * ∑ j, (homogenizedCoefficient Q j i : ℂ) *
        c4EndpointPairing Q u (homogeneousGaussianHorizontalGradient Q i s hs (-ξ) g j) := by
  let F := fun f : Lp ℂ 2 (reducedLaw Q) =>
    c4EndpointPairing Q u (c3GaussianTimeDerivativeCLM Q i s hs (-ξ) f)
  let H := fun f : Lp ℂ 2 (reducedLaw Q) =>
    -(1 / 2 : ℂ) * ∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
      c4EndpointPairing Q (G j) (homogeneousGaussianHorizontalGradient Q i s hs (-ξ) f k) -
    ξ * ∑ j, (homogenizedCoefficient Q j i : ℂ) *
      c4EndpointPairing Q u (homogeneousGaussianHorizontalGradient Q i s hs (-ξ) f j)
  have hF : Continuous F := (c4EndpointPairing Q u).continuous.comp
    (c3GaussianTimeDerivativeCLM Q i s hs (-ξ)).continuous
  have hH : Continuous H := by
    apply Continuous.sub
    · apply continuous_const.mul
      apply continuous_finsetSum
      intro j _
      apply continuous_finsetSum
      intro k _
      exact continuous_const.mul ((c4EndpointPairing Q (G j)).continuous.comp
        (continuous_homogeneousGaussianHorizontalGradient Q i s hs (-ξ) k))
    · apply continuous_const.mul
      apply continuous_finsetSum
      intro j _
      exact continuous_const.mul ((c4EndpointPairing Q u).continuous.comp
        (continuous_homogeneousGaussianHorizontalGradient Q i s hs (-ξ) j))
  have hclosed := isClosed_eq hF hH
  have hsubset : {f | IsComplexHorizontallySmooth Q f} ⊆ {f | F f = H f} := by
    intro f hf
    obtain ⟨K, hK0, hK⟩ := hf
    have hgrad : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
        (homogeneousAverage Q i s hs (-ξ) f)
        (fun j => homogeneousAverage Q i s hs (-ξ) (K [j])) := by
      intro j
      have hj := (hK [] j).homogeneousAverage i s hs (-ξ)
      rw [hK0] at hj
      exact hj
    have he := (homogeneousAverage_hasComplexHorizontalGradient_allData Q i s hs (-ξ) f).unique hgrad
    have hw := homogeneousGaussianEvolutionTimeDerivative_negativeForce_horizontalJet_weak
      Q i s hs ξ K hK u G hu
    rw [hK0] at hw
    change F f = H f
    dsimp only [F, H]
    rw [he]
    change c4EndpointPairing Q u (∫ x : Vec d,
      homogenizedGaussianKernelTimeDerivative Q i s hs (-ξ) x •
        complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) = _
    simpa only [c4EndpointPairing_apply, homogeneousGaussianEvolutionTimeDerivative,
      dite_eq_left hs] using! hw
  have heq := hclosed.closure_subset (closure_mono hsubset (dense_complexHorizontallySmooth Q g))
  change F g = H g at heq
  simpa only [F, H, c3GaussianTimeDerivativeCLM, LinearMap.mkContinuous_apply,
    homogeneousGaussianEvolutionTimeDerivative, dite_eq_left hs] using! heq

/-- The stationary equation cancels the principal and signed drift terms of
an actual backward homogeneous test. The forward centered source is retained. -/
theorem c3CenteredEndpoint_backwardJet_hasDerivAt
    (hc : Blueprint.node_e_u3A_centered_u2D_equationsStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (K : List (Fin d) → Lp ℂ 2 (reducedLaw Q)) (hK : HasComplexHorizontalJet Q K)
    (T t : ℝ) (ht : 0 < t) (htT : t < T) :
    let U := fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal
    let ξ := (endpointDriftSign ν : ℂ) * ζ
    let v := homogeneousAverage Q ⟨0, by omega⟩ (T - t) (sub_pos.mpr htT) (-ξ) (K [])
    let W := fun j => homogeneousAverage Q ⟨0, by omega⟩ (T - t) (sub_pos.mpr htT) (-ξ) (K [j])
    ∃ G J : Fin d → Lp ℂ 2 (reducedLaw Q),
      IsEndpointWeakFlux hd Q ν ζ a (U t) G J ∧
      HasDerivAt (fun s : ℝ => c4EndpointPairing Q (U s)
        (homogeneousGaussianEvolution Q ⟨0, by omega⟩ (-ξ) (T - s).toNNReal (K [])))
        (-(1 / 2 : ℂ) * (∫ ω, ∑ j, J j ω * W j ω ∂reducedLaw Q) +
          c4EndpointSourceCoefficient ν ζ *
            (∫ ω, (J ⟨0, by omega⟩ ω - ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) *
              v ω ∂reducedLaw Q)) t := by
  dsimp only
  let U := fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal
  let ξ := (endpointDriftSign ν : ℂ) * ζ
  let v := homogeneousAverage Q ⟨0, by omega⟩ (T - t) (sub_pos.mpr htT) (-ξ) (K [])
  let W := fun j => homogeneousAverage Q ⟨0, by omega⟩ (T - t) (sub_pos.mpr htT) (-ξ) (K [j])
  obtain ⟨G, J, V, hflux, hV, hstat⟩ :=
    c4IndexedEndpoint_stationaryFlux hc hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
      t.toNNReal (by simpa only [Real.coe_toNNReal t ht.le] using ht)
  rw [Real.coe_toNNReal t ht.le] at hV
  have hW : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v W :=
    fun j => (hK [] j).homogeneousAverage ⟨0, by omega⟩ (T - t) (sub_pos.mpr htT) (-ξ)
  have hs := hstat v W hW
  have hg := homogeneousGaussianEvolutionTimeDerivative_negativeForce_horizontalJet_weak
    Q ⟨0, by omega⟩ (T - t) (sub_pos.mpr htT) ξ K hK (U t) G hflux.1
  have hsym : (∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
      (∫ ω, G j ω * W k ω ∂reducedLaw Q)) =
      ∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
        (∫ ω, G k ω * W j ω ∂reducedLaw Q) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    have he : homogenizedCoefficient Q k j = homogenizedCoefficient Q j k :=
      homogenizedMatrix_apply_comm Q k j
    rw [he]
  have hdrift (j : Fin d) : (∫ ω, U t ω * W j ω ∂reducedLaw Q) =
      -(∫ ω, G j ω * v ω ∂reducedLaw Q) := by
    have hb := (complexHorizontalDerivatives_integration_by_parts (hflux.1 j) (hW j)).2.2
    simpa only [neg_neg] using! congrArg Neg.neg hb.symm
  change _ = -(1 / 2 : ℂ) * (∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
    (∫ ω, G j ω * W k ω ∂reducedLaw Q)) - ξ *
      ∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) *
        (∫ ω, U t ω * W j ω ∂reducedLaw Q) at hg
  rw [hsym] at hg
  simp_rw [hdrift, mul_neg, Finset.sum_neg_distrib] at hg
  have hprod (f g : Lp ℂ 2 (reducedLaw Q)) :
      Integrable (fun ω => f ω * g ω) (reducedLaw Q) :=
    (Lp.memLp f).integrable_mul (Lp.memLp g)
  have hprincipal : (∫ ω, ∑ j, ((∑ k, (homogenizedCoefficient Q j k : ℂ) * G k ω) + J j ω) *
      W j ω ∂reducedLaw Q) =
      (∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
        (∫ ω, G k ω * W j ω ∂reducedLaw Q)) +
      (∫ ω, ∑ j, J j ω * W j ω ∂reducedLaw Q) := by
    simp_rw [add_mul, Finset.sum_mul, Finset.sum_add_distrib]
    rw [integral_add
      (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
        by simpa only [mul_assoc] using (hprod (G k) (W j)).const_mul (homogenizedCoefficient Q j k : ℂ))
      (integrable_finsetSum _ fun j _ => hprod (J j) (W j))]
    congr 1
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl fun k _ => by
          have he : (fun ω => (homogenizedCoefficient Q j k : ℂ) * G k ω * W j ω) =
              (fun ω => (homogenizedCoefficient Q j k : ℂ) * (G k ω * W j ω)) := by
            funext ω
            exact mul_assoc _ _ _
          rw [he, integral_const_mul]
      · intro k _
        simpa only [mul_assoc] using (hprod (G k) (W j)).const_mul (homogenizedCoefficient Q j k : ℂ)
    · intro j _
      exact integrable_finsetSum _ fun k _ => by
        simpa only [mul_assoc] using (hprod (G k) (W j)).const_mul (homogenizedCoefficient Q j k : ℂ)
  have hD : Integrable (fun ω => (∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω)
      (reducedLaw Q) := by
    simp_rw [Finset.sum_mul]
    exact integrable_finsetSum _ fun j _ => by
      simpa only [mul_assoc] using (hprod (G j) v).const_mul (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ)
  have hS := hprod (J ⟨0, by omega⟩) v
  have hcenter : Integrable (fun ω => (J ⟨0, by omega⟩ ω - ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * v ω)
      (reducedLaw Q) := by
    simpa only [sub_mul, Pi.sub_apply] using! hS.sub (((Lp.memLp v).integrable one_le_two).const_mul _)
  have hright : (∫ ω, (2 : ℂ) * (V ω - ξ * (∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) *
      G j ω) - c4EndpointSourceCoefficient ν ζ * (J ⟨0, by omega⟩ ω -
        ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q)) * v ω ∂reducedLaw Q) =
      2 * ((∫ ω, V ω * v ω ∂reducedLaw Q) -
        ξ * (∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) *
          (∫ ω, G j ω * v ω ∂reducedLaw Q)) - c4EndpointSourceCoefficient ν ζ *
            (∫ ω, (J ⟨0, by omega⟩ ω - ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * v ω ∂reducedLaw Q)) := by
    have he : (fun ω => (2 : ℂ) * (V ω - ξ * (∑ j,
        (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) -
          c4EndpointSourceCoefficient ν ζ * (J ⟨0, by omega⟩ ω -
            ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q)) * v ω) =
        (fun ω => 2 * ((V ω * v ω - ξ * ((∑ j,
          (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω)) -
          c4EndpointSourceCoefficient ν ζ * ((J ⟨0, by omega⟩ ω -
            ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * v ω))) := by
      funext ω
      ring
    have hfirst : Integrable (fun ω => V ω * v ω - ξ * ((∑ j,
        (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω)) (reducedLaw Q) :=
      (hprod V v).sub (hD.const_mul ξ)
    have hsecond : Integrable (fun ω => c4EndpointSourceCoefficient ν ζ *
        ((J ⟨0, by omega⟩ ω - ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * v ω))
        (reducedLaw Q) := hcenter.const_mul _
    have hsplit : (∫ ω, (V ω * v ω - ξ * ((∑ j,
        (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω)) -
        c4EndpointSourceCoefficient ν ζ * ((J ⟨0, by omega⟩ ω -
          ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * v ω) ∂reducedLaw Q) =
        (∫ ω, V ω * v ω - ξ * ((∑ j,
          (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω) ∂reducedLaw Q) -
        (∫ ω, c4EndpointSourceCoefficient ν ζ * ((J ⟨0, by omega⟩ ω -
          ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * v ω) ∂reducedLaw Q) :=
      integral_sub hfirst hsecond
    have hinner : (∫ ω, V ω * v ω - ξ * ((∑ j,
        (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω) ∂reducedLaw Q) =
        (∫ ω, V ω * v ω ∂reducedLaw Q) -
        (∫ ω, ξ * ((∑ j,
          (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω) ∂reducedLaw Q) :=
      integral_sub (hprod V v) (hD.const_mul ξ)
    rw [he, integral_const_mul, hsplit, hinner, integral_const_mul, integral_const_mul]
    have hde : (∫ ω, (∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω
        ∂reducedLaw Q) = ∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) *
          (∫ ω, G j ω * v ω ∂reducedLaw Q) := by
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum _ (fun j _ => by
        simpa only [mul_assoc] using (hprod (G j) v).const_mul (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ))]
      apply Finset.sum_congr rfl
      intro j _
      have hfun : (fun ω => (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω * v ω) =
          (fun ω => (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * (G j ω * v ω)) := by
        funext ω
        exact mul_assoc _ _ _
      rw [hfun, integral_const_mul]
    rw [hde]
  rw [hprincipal, hright] at hs
  refine ⟨G, J, hflux, ?_⟩
  have hdv := c4BackwardGaussian_hasDerivAt Q ⟨0, by omega⟩ ξ (K []) T t htT hV
  have htime : ((T - t).toNNReal : ℝ) = T - t := Real.coe_toNNReal _ (sub_pos.mpr htT).le
  rw [homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ (-ξ) (T - t).toNNReal
    (by rw [htime]; exact sub_pos.mpr htT)] at hdv
  simp only [htime] at hdv
  apply hdv.congr_deriv
  rw [c4EndpointPairing_apply, c4EndpointPairing_apply]
  change (∫ ω, V ω * v ω ∂reducedLaw Q) - _ = _
  rw [hg]
  linear_combination (1 / 2 : ℂ) * hs

/-- The stationary equation cancels the principal and signed drift terms of
an actual backward homogeneous test. The forward centered source is retained. -/
theorem c3CenteredEndpoint_backwardL2_hasDerivAt
    (hc : Blueprint.node_e_u3A_centered_u2D_equationsStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (g : Lp ℂ 2 (reducedLaw Q))
    (T t : ℝ) (ht : 0 < t) (htT : t < T) :
    let U := fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal
    let ξ := (endpointDriftSign ν : ℂ) * ζ
    let v := homogeneousAverage Q ⟨0, by omega⟩ (T - t) (sub_pos.mpr htT) (-ξ) g
    let W := homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ (T - t) (sub_pos.mpr htT) (-ξ) g
    ∃ G J : Fin d → Lp ℂ 2 (reducedLaw Q),
      IsEndpointWeakFlux hd Q ν ζ a (U t) G J ∧
      HasDerivAt (fun s : ℝ => c4EndpointPairing Q (U s)
        (homogeneousGaussianEvolution Q ⟨0, by omega⟩ (-ξ) (T - s).toNNReal g))
        (-(1 / 2 : ℂ) * (∫ ω, ∑ j, J j ω * W j ω ∂reducedLaw Q) +
          c4EndpointSourceCoefficient ν ζ *
            (∫ ω, (J ⟨0, by omega⟩ ω - ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) *
              v ω ∂reducedLaw Q)) t := by
  dsimp only
  let U := fun s : ℝ => indexedEndpoint hd Q ν ζ P Pdag β a μ s.toNNReal
  let ξ := (endpointDriftSign ν : ℂ) * ζ
  let v := homogeneousAverage Q ⟨0, by omega⟩ (T - t) (sub_pos.mpr htT) (-ξ) g
  let W := homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ (T - t) (sub_pos.mpr htT) (-ξ) g
  obtain ⟨G, J, V, hflux, hV, hstat⟩ :=
    c4IndexedEndpoint_stationaryFlux hc hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
      t.toNNReal (by simpa only [Real.coe_toNNReal t ht.le] using ht)
  rw [Real.coe_toNNReal t ht.le] at hV
  have hW : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v W :=
    homogeneousAverage_hasComplexHorizontalGradient_allData Q ⟨0, by omega⟩
      (T - t) (sub_pos.mpr htT) (-ξ) g
  have hs := hstat v W hW
  have hg := c3GaussianTimeDerivative_negativeForce_weak
    Q ⟨0, by omega⟩ (T - t) (sub_pos.mpr htT) ξ (U t) G hflux.1 g
  simp only [c4EndpointPairing_apply] at hg
  have hsym : (∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
      (∫ ω, G j ω * W k ω ∂reducedLaw Q)) =
      ∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
        (∫ ω, G k ω * W j ω ∂reducedLaw Q) := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    have he : homogenizedCoefficient Q k j = homogenizedCoefficient Q j k :=
      homogenizedMatrix_apply_comm Q k j
    rw [he]
  have hdrift (j : Fin d) : (∫ ω, U t ω * W j ω ∂reducedLaw Q) =
      -(∫ ω, G j ω * v ω ∂reducedLaw Q) := by
    have hb := (complexHorizontalDerivatives_integration_by_parts (hflux.1 j) (hW j)).2.2
    simpa only [neg_neg] using! congrArg Neg.neg hb.symm
  change _ = -(1 / 2 : ℂ) * (∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
    (∫ ω, G j ω * W k ω ∂reducedLaw Q)) - ξ *
      ∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) *
        (∫ ω, U t ω * W j ω ∂reducedLaw Q) at hg
  rw [hsym] at hg
  simp_rw [hdrift, mul_neg, Finset.sum_neg_distrib] at hg
  have hprod (f g : Lp ℂ 2 (reducedLaw Q)) :
      Integrable (fun ω => f ω * g ω) (reducedLaw Q) :=
    (Lp.memLp f).integrable_mul (Lp.memLp g)
  have hprincipal : (∫ ω, ∑ j, ((∑ k, (homogenizedCoefficient Q j k : ℂ) * G k ω) + J j ω) *
      W j ω ∂reducedLaw Q) =
      (∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
        (∫ ω, G k ω * W j ω ∂reducedLaw Q)) +
      (∫ ω, ∑ j, J j ω * W j ω ∂reducedLaw Q) := by
    simp_rw [add_mul, Finset.sum_mul, Finset.sum_add_distrib]
    rw [integral_add
      (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
        by simpa only [mul_assoc] using (hprod (G k) (W j)).const_mul (homogenizedCoefficient Q j k : ℂ))
      (integrable_finsetSum _ fun j _ => hprod (J j) (W j))]
    congr 1
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro j _
      rw [integral_finsetSum]
      · exact Finset.sum_congr rfl fun k _ => by
          have he : (fun ω => (homogenizedCoefficient Q j k : ℂ) * G k ω * W j ω) =
              (fun ω => (homogenizedCoefficient Q j k : ℂ) * (G k ω * W j ω)) := by
            funext ω
            exact mul_assoc _ _ _
          rw [he, integral_const_mul]
      · intro k _
        simpa only [mul_assoc] using (hprod (G k) (W j)).const_mul (homogenizedCoefficient Q j k : ℂ)
    · intro j _
      exact integrable_finsetSum _ fun k _ => by
        simpa only [mul_assoc] using (hprod (G k) (W j)).const_mul (homogenizedCoefficient Q j k : ℂ)
  have hD : Integrable (fun ω => (∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω)
      (reducedLaw Q) := by
    simp_rw [Finset.sum_mul]
    exact integrable_finsetSum _ fun j _ => by
      simpa only [mul_assoc] using (hprod (G j) v).const_mul (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ)
  have hS := hprod (J ⟨0, by omega⟩) v
  have hcenter : Integrable (fun ω => (J ⟨0, by omega⟩ ω - ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * v ω)
      (reducedLaw Q) := by
    simpa only [sub_mul, Pi.sub_apply] using! hS.sub (((Lp.memLp v).integrable one_le_two).const_mul _)
  have hright : (∫ ω, (2 : ℂ) * (V ω - ξ * (∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) *
      G j ω) - c4EndpointSourceCoefficient ν ζ * (J ⟨0, by omega⟩ ω -
        ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q)) * v ω ∂reducedLaw Q) =
      2 * ((∫ ω, V ω * v ω ∂reducedLaw Q) -
        ξ * (∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) *
          (∫ ω, G j ω * v ω ∂reducedLaw Q)) - c4EndpointSourceCoefficient ν ζ *
            (∫ ω, (J ⟨0, by omega⟩ ω - ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * v ω ∂reducedLaw Q)) := by
    have he : (fun ω => (2 : ℂ) * (V ω - ξ * (∑ j,
        (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) -
          c4EndpointSourceCoefficient ν ζ * (J ⟨0, by omega⟩ ω -
            ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q)) * v ω) =
        (fun ω => 2 * ((V ω * v ω - ξ * ((∑ j,
          (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω)) -
          c4EndpointSourceCoefficient ν ζ * ((J ⟨0, by omega⟩ ω -
            ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * v ω))) := by
      funext ω
      ring
    have hfirst : Integrable (fun ω => V ω * v ω - ξ * ((∑ j,
        (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω)) (reducedLaw Q) :=
      (hprod V v).sub (hD.const_mul ξ)
    have hsecond : Integrable (fun ω => c4EndpointSourceCoefficient ν ζ *
        ((J ⟨0, by omega⟩ ω - ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * v ω))
        (reducedLaw Q) := hcenter.const_mul _
    have hsplit : (∫ ω, (V ω * v ω - ξ * ((∑ j,
        (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω)) -
        c4EndpointSourceCoefficient ν ζ * ((J ⟨0, by omega⟩ ω -
          ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * v ω) ∂reducedLaw Q) =
        (∫ ω, V ω * v ω - ξ * ((∑ j,
          (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω) ∂reducedLaw Q) -
        (∫ ω, c4EndpointSourceCoefficient ν ζ * ((J ⟨0, by omega⟩ ω -
          ∫ ω', J ⟨0, by omega⟩ ω' ∂reducedLaw Q) * v ω) ∂reducedLaw Q) :=
      integral_sub hfirst hsecond
    have hinner : (∫ ω, V ω * v ω - ξ * ((∑ j,
        (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω) ∂reducedLaw Q) =
        (∫ ω, V ω * v ω ∂reducedLaw Q) -
        (∫ ω, ξ * ((∑ j,
          (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω) ∂reducedLaw Q) :=
      integral_sub (hprod V v) (hD.const_mul ξ)
    rw [he, integral_const_mul, hsplit, hinner, integral_const_mul, integral_const_mul]
    have hde : (∫ ω, (∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω) * v ω
        ∂reducedLaw Q) = ∑ j, (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) *
          (∫ ω, G j ω * v ω ∂reducedLaw Q) := by
      simp_rw [Finset.sum_mul]
      rw [integral_finsetSum _ (fun j _ => by
        simpa only [mul_assoc] using (hprod (G j) v).const_mul (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ))]
      apply Finset.sum_congr rfl
      intro j _
      have hfun : (fun ω => (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * G j ω * v ω) =
          (fun ω => (homogenizedCoefficient Q j ⟨0, by omega⟩ : ℂ) * (G j ω * v ω)) := by
        funext ω
        exact mul_assoc _ _ _
      rw [hfun, integral_const_mul]
    rw [hde]
  rw [hprincipal, hright] at hs
  refine ⟨G, J, hflux, ?_⟩
  have hdv := c4BackwardGaussian_hasDerivAt Q ⟨0, by omega⟩ ξ g T t htT hV
  have htime : ((T - t).toNNReal : ℝ) = T - t := Real.coe_toNNReal _ (sub_pos.mpr htT).le
  rw [homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ (-ξ) (T - t).toNNReal
    (by rw [htime]; exact sub_pos.mpr htT)] at hdv
  simp only [htime] at hdv
  apply hdv.congr_deriv
  rw [c4EndpointPairing_apply, c4EndpointPairing_apply]
  change (∫ ω, V ω * v ω ∂reducedLaw Q) - _ = _
  rw [hg]
  linear_combination (1 / 2 : ℂ) * hs

/-- The actual backward interaction reaches its physical terminal pairing.
The initial backward datum may already include the positive Gaussian smoothing. -/
theorem c3CenteredEndpoint_backward_terminal
    (hc : Blueprint.node_e_u3A_centered_u2D_equationsStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (g : Lp ℂ 2 (reducedLaw Q))
    (T : ℝ) (hT : 0 < T) :
    Filter.Tendsto (fun t : ℝ => c4EndpointPairing Q
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t.toNNReal)
      (homogeneousGaussianEvolution Q ⟨0, by omega⟩
        (-((endpointDriftSign ν : ℂ) * ζ)) (T - t).toNNReal g))
      (nhds T) (nhds (c4EndpointPairing Q
        (indexedEndpoint hd Q ν ζ P Pdag β a μ T.toNNReal) g)) := by
  have hu := (c4IndexedEndpoint_differentiableAt hc hd D Q hQ β a μ hβ ha hμ
    ζ P Pdag hP hPdag ν T hT).continuousAt
  have hv : ContinuousAt (fun t : ℝ => homogeneousGaussianEvolution Q ⟨0, by omega⟩
      (-((endpointDriftSign ν : ℂ) * ζ)) (T - t).toNNReal g) T :=
    ((continuous_homogeneousGaussianEvolution Q ⟨0, by omega⟩
      (-((endpointDriftSign ν : ℂ) * ζ)) g).comp
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))).continuousAt
  have hp := ((c4EndpointPairing Q).continuous.continuousAt.comp hu).clm_apply hv
  simpa only [sub_self, Real.toNNReal_zero, homogeneousGaussianEvolution_zero,
    ContinuousLinearMap.id_apply] using! hp.tendsto

/-- Divergence testing sees precisely the centered flux, since every genuine
horizontal derivative has mean zero. -/
theorem c3EndpointPairing_centered_gradient {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (v : Lp ℂ 2 (reducedLaw Q))
    (W : Fin d → Lp ℂ 2 (reducedLaw Q))
    (hW : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v W)
    (f : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    c4EndpointPairing Q f (W j) = c4EndpointPairing Q (centeredComplexLp Q f) (W j) := by
  have hzero : c4EndpointPairing Q
      (Lp.const 2 (reducedLaw Q) (∫ ω, f ω ∂reducedLaw Q)) (W j) = 0 := by
    rw [c4EndpointPairing_apply]
    calc
      _ = ∫ ω, (∫ ω', f ω' ∂reducedLaw Q) * W j ω ∂reducedLaw Q := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (∫ ω, f ω ∂reducedLaw Q)] with ω hω
        rw [hω]
        rfl
      _ = 0 := by rw [integral_const_mul, (hW j).integral_eq_zero, mul_zero]
  simp only [centeredComplexLp, map_sub, sub_apply, hzero, sub_zero]

/-- The physical bilinear pairing has the sharp L2 product bound. -/
theorem c3EndpointPairing_norm_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (f g : Lp ℂ 2 (reducedLaw Q)) :
    ‖c4EndpointPairing Q f g‖ ≤ ‖f‖ * ‖g‖ := by
  rw [c4EndpointPairing_apply, ← inner_complexL2Conjugation_eq_integral_mul]
  simpa only [norm_complexL2Conjugation] using
    norm_inner_le_norm (complexL2Conjugation (reducedLaw Q) f) g

/-- Bilinear testing against every actual L2 datum detects the actual L2 norm.
The test is the conjugate of the physical output itself. -/
theorem c3Norm_le_of_endpointPairing_bound {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (f : Lp ℂ 2 (reducedLaw Q)) {C : ℝ} (hC : 0 ≤ C)
    (hbound : ∀ g : Lp ℂ 2 (reducedLaw Q), ‖c4EndpointPairing Q f g‖ ≤ C * ‖g‖) :
    ‖f‖ ≤ C := by
  have h := hbound (complexL2Conjugation (reducedLaw Q) f)
  simp only [c4EndpointPairing_apply, ← inner_complexL2Conjugation_eq_integral_mul,
    inner_self_eq_norm_sq_to_K, norm_pow, RCLike.norm_ofReal, abs_norm,
    norm_complexL2Conjugation] at h
  by_cases hf : f = 0
  · simpa only [hf, norm_zero] using hC
  · have hpos := norm_pos_iff.mpr hf
    nlinarith

/-- Spatial Schwartz averaging commutes with the actual homogeneous evolution,
including zero time and arbitrary signed complex force. -/
theorem c3SchwartzAverage_homogeneousEvolution {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (ψ : SchwartzMap (Vec d) ℂ) (f : Lp ℂ 2 (reducedLaw Q)) :
    stationarySchwartzAverage Q ψ (homogeneousGaussianEvolution Q i ζ t f) =
      homogeneousGaussianEvolution Q i ζ t (stationarySchwartzAverage Q ψ f) := by
  unfold stationarySchwartzAverage
  rw [← (homogeneousGaussianEvolution Q i ζ t).integral_comp_comm
    (integrable_stationarySchwartzAverage_integrand Q ψ f)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    simp only [map_smul, complexTranslation_homogeneousGaussianEvolution]

/-- The unforced derivative kernel is odd in its spatial argument. -/
theorem c3UnforcedGaussian_coordinateDerivative_neg {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i j : Fin d) (s : ℝ) (hs : 0 < s) (x : Vec d) :
    fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) (-x) (unitVector j) =
      -fderiv ℝ (homogenizedGaussianKernel Q i s hs 0) x (unitVector j) := by
  have hK : homogenizedGaussianKernel Q i s hs 0 (-x) =
      homogenizedGaussianKernel Q i s hs 0 x := by
    simpa only [neg_zero] using (homogenizedGaussianKernel_neg_force Q i s hs 0 x).symm
  rw [fderiv_homogenizedGaussianKernel_complexForce_coordinate,
    fderiv_homogenizedGaussianKernel_complexForce_coordinate, hK]
  simp only [Matrix.mulVec_neg, Pi.neg_apply, Complex.ofReal_neg, zero_mul]
  ring

/-- The first frozen derivative average is exactly the strong horizontal
coordinate derivative of the unforced Gaussian average. -/
theorem c3GaussianDerivativeAverage_one_eq_gradient {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s)
    (f : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) f =
      homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ s hs 0 f j := by
  unfold gaussianDerivativeAverage homogeneousGaussianHorizontalGradient
  simp only [iteratedFDeriv_one_apply, c3UnforcedGaussian_coordinateDerivative_neg,
    neg_smul, integral_neg]

/-- Every frozen Gaussian derivative average commutes with the actual
homogeneous evolution, preserving its literal anisotropic kernel. -/
theorem c3GaussianDerivativeAverage_homogeneousEvolution {d : ℕ} (hd : 2 ≤ d)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ) (t : ℝ≥0)
    (s : ℝ) (hs : 0 < s) (k : ℕ) (dirs : Fin k → Fin d)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    gaussianDerivativeAverage hd Q s hs k dirs (homogeneousGaussianEvolution Q i ζ t f) =
      homogeneousGaussianEvolution Q i ζ t (gaussianDerivativeAverage hd Q s hs k dirs f) := by
  simpa only [stationarySchwartzAverage, unforcedGaussianDerivativeSchwartz_apply,
    gaussianDerivativeAverage] using
    c3SchwartzAverage_homogeneousEvolution Q i ζ t
      (unforcedGaussianDerivativeSchwartz Q ⟨0, by omega⟩ s hs k dirs) f

/-- The bilinear transpose of first Gaussian differentiation has the required
minus sign, with no complex conjugation of either physical field. -/
theorem c3EndpointPairing_gaussianDerivativeAverage_one {d : ℕ} (hd : 2 ≤ d)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s)
    (f g : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    c4EndpointPairing Q (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) f) g =
      -c4EndpointPairing Q f (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) g) := by
  have h := S3Dual.integral_tavg_mul_eq Q
    (integrable_gaussianDerivativeKernel Q ⟨0, by omega⟩ s hs 1 (fun _ => j))
    (continuous_gaussianDerivativeKernel Q ⟨0, by omega⟩ s hs 1 (fun _ => j)) f g
  have he : S3Dual.tavg Q (fun x : Vec d => iteratedFDeriv ℝ 1
      (homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0) (-(-x))
        (fun _ => unitVector j)) g =
      -gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) g := by
    simp only [S3Dual.tavg, gaussianDerivativeAverage, iteratedFDeriv_one_apply,
      neg_neg, c3UnforcedGaussian_coordinateDerivative_neg, neg_smul, integral_neg]
  rw [he] at h
  have h' : c4EndpointPairing Q (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) f) g =
      c4EndpointPairing Q f (-gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) g) := by
    simpa only [c4EndpointPairing_apply, gaussianDerivativeAverage, S3Dual.tavg] using h
  simpa only [map_neg] using h'

/-- Smoothing the datum before the backward evolution puts its horizontal
derivative on the smoothing kernel, at any positive backward time. -/
theorem c3HomogeneousGradient_smoothed {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ) (t : ℝ≥0) (ht : 0 < (t : ℝ))
    (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    homogeneousGaussianHorizontalGradient Q i t ht ζ (gaussianAverage hd Q s hs g) j =
      homogeneousGaussianEvolution Q i ζ t
        (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) g) := by
  have h := (homogeneousAverage_hasComplexHorizontalGradient_allData Q
    ⟨0, by omega⟩ s hs 0 g j).homogeneousGaussianEvolution i ζ t
  have h' := homogeneousGaussianEvolution_hasComplexHorizontalGradient_allData Q i ζ t ht
    (gaussianAverage hd Q s hs g) j
  rw [c3GaussianDerivativeAverage_one_eq_gradient]
  exact h'.unique h

/-- Moving the differentiated smoothed homogeneous test to the physical field
reverses the force and retains the horizontal integration sign. -/
theorem c3EndpointPairing_homogeneousSmoothedGradient {d : ℕ} (hd : 2 ≤ d)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (s : ℝ) (hs : 0 < s)
    (f g : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    c4EndpointPairing Q f
      (homogeneousGaussianHorizontalGradient Q i t ht ζ (gaussianAverage hd Q s hs g) j) =
      -c4EndpointPairing Q (homogeneousGaussianEvolution Q i (-ζ) t
        (gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) f)) g := by
  rw [c3HomogeneousGradient_smoothed]
  have htrans : ∀ v : Lp ℂ 2 (reducedLaw Q),
      c4EndpointPairing Q f (homogeneousGaussianEvolution Q i ζ t v) =
        c4EndpointPairing Q (homogeneousGaussianEvolution Q i (-ζ) t f) v := by
    intro v
    simp only [homogeneousGaussianEvolution_pos Q i ζ t ht,
      homogeneousGaussianEvolution_pos Q i (-ζ) t ht]
    simpa only [neg_neg] using (c4EndpointPairing_homogeneousAverage Q i t ht (-ζ) f v).symm
  rw [htrans]
  rw [← c3GaussianDerivativeAverage_homogeneousEvolution]
  rw [c3EndpointPairing_gaussianDerivativeAverage_one, neg_neg]

/-- Only the smoothed flux derivative is needed to control a differentiated
backward test; homogeneous growth is the actual structural operator bound. -/
theorem c3EndpointPairing_homogeneousSmoothedGradient_norm_le {d : ℕ} (hd : 2 ≤ d)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (s : ℝ) (hs : 0 < s)
    (f g : Lp ℂ 2 (reducedLaw Q)) (j : Fin d) :
    ‖c4EndpointPairing Q f
      (homogeneousGaussianHorizontalGradient Q i t ht ζ (gaussianAverage hd Q s hs g) j)‖ ≤
      Real.exp (sourceReducedBound Λ * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
        ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) f‖ * ‖g‖ := by
  rw [c3EndpointPairing_homogeneousSmoothedGradient, norm_neg]
  refine (c3EndpointPairing_norm_le Q _ g).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg g)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (by simpa only [norm_neg] using norm_homogeneousGaussianEvolution_le Q i (-ζ) t)
      (norm_nonneg _))

/-- The zeroth frozen derivative average is the actual unforced Gaussian
smoothing operator, with its reflected argument removed by evenness. -/
theorem c3GaussianDerivativeAverage_zero {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (s : ℝ) (hs : 0 < s)
    (dirs : Fin 0 → Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    gaussianDerivativeAverage hd Q s hs 0 dirs f = gaussianAverage hd Q s hs f := by
  unfold gaussianDerivativeAverage gaussianAverage
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  simp only [iteratedFDeriv_zero_apply]
  have h := homogenizedGaussianKernel_neg_force Q ⟨0, by omega⟩ s hs 0 x
  simpa only [neg_zero] using congrArg (fun z : ℂ => z •
    complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) h.symm

/-- The source part of the backward test only requires the unforced smoothed
physical flux, followed by the actual structural homogeneous growth bound. -/
theorem c3EndpointPairing_homogeneousSmoothed_norm_le {d : ℕ} (hd : 2 ≤ d)
    {Λ r : ℝ} (Q : EnvironmentLaw d Λ r) (i : Fin d) (ζ : ℂ)
    (t : ℝ≥0) (ht : 0 < (t : ℝ)) (s : ℝ) (hs : 0 < s)
    (f g : Lp ℂ 2 (reducedLaw Q)) :
    ‖c4EndpointPairing Q f
      (homogeneousAverage Q i t ht ζ (gaussianAverage hd Q s hs g))‖ ≤
      Real.exp (sourceReducedBound Λ * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
        ‖gaussianAverage hd Q s hs f‖ * ‖g‖ := by
  have hcomm : gaussianAverage hd Q s hs (homogeneousGaussianEvolution Q i (-ζ) t f) =
      homogeneousGaussianEvolution Q i (-ζ) t (gaussianAverage hd Q s hs f) := by
    simpa only [c3GaussianDerivativeAverage_zero] using
      c3GaussianDerivativeAverage_homogeneousEvolution hd Q i (-ζ) t s hs 0
        (fun j => Fin.elim0 j) f
  have he : c4EndpointPairing Q f
      (homogeneousAverage Q i t ht ζ (gaussianAverage hd Q s hs g)) =
      c4EndpointPairing Q (homogeneousGaussianEvolution Q i (-ζ) t
        (gaussianAverage hd Q s hs f)) g := by
    rw [← hcomm]
    change c4EndpointPairing Q f
      (homogeneousAverage Q i t ht ζ (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 g)) =
      c4EndpointPairing Q (homogeneousAverage Q ⟨0, by omega⟩ s hs 0
        (homogeneousGaussianEvolution Q i (-ζ) t f)) g
    rw [c4EndpointPairing_homogeneousAverage, neg_zero,
      homogeneousGaussianEvolution_pos Q i (-ζ) t ht,
      c4EndpointPairing_homogeneousAverage, neg_neg]
  rw [he]
  refine (c3EndpointPairing_norm_le Q _ g).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg g)
  exact (ContinuousLinearMap.le_opNorm _ _).trans
    (mul_le_mul_of_nonneg_right
      (by simpa only [norm_neg] using norm_homogeneousGaussianEvolution_le Q i (-ζ) t)
      (norm_nonneg _))

/-- The literal physical flux functional for the backward homogeneous test.
Its value outside the open backward-time interval is irrelevant to integration. -/
def c3BackwardFluxFunctional {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (ζ : ℂ) (T : ℝ)
    (J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (g : Lp ℂ 2 (reducedLaw Q)) (t : ℝ) : ℂ :=
  if ht : t < T then
    -(1 / 2 : ℂ) * (∫ ω, ∑ j, J t.toNNReal j ω *
      homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ (T - t)
        (sub_pos.mpr ht) (-((endpointDriftSign ν : ℂ) * ζ)) g j ω ∂reducedLaw Q) +
    c4EndpointSourceCoefficient ν ζ *
      (∫ ω, (J t.toNNReal ⟨0, by omega⟩ ω -
        ∫ ω', J t.toNNReal ⟨0, by omega⟩ ω' ∂reducedLaw Q) *
        homogeneousAverage Q ⟨0, by omega⟩ (T - t) (sub_pos.mpr ht)
          (-((endpointDriftSign ν : ℂ) * ζ)) g ω ∂reducedLaw Q)
  else 0

/-- A physical backward flux test is controlled by the centered flux's actual
zeroth and first Gaussian averages. No flux regularity or measurability is
assumed, and both the signed force and the endpoint source are retained. -/
theorem c3BackwardFluxFunctional_smoothed_norm_le {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (ζ : ℂ) (T t : ℝ) (ht : t < T)
    (J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q)) :
    let F := fun j => centeredComplexLp Q (J t.toNNReal j)
    ‖c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g) t‖ ≤
      Real.exp (sourceReducedBound Λ * ‖-((endpointDriftSign ν : ℂ) * ζ)‖ ^ 2 *
        (T - t) / 2) *
      ((1 / 2 : ℝ) * (∑ j, ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) (F j)‖) +
        ‖c4EndpointSourceCoefficient ν ζ‖ *
          ‖gaussianAverage hd Q s hs (F ⟨0, by omega⟩)‖) * ‖g‖ := by
  dsimp only
  let F := fun j => centeredComplexLp Q (J t.toNNReal j)
  let ξ := -((endpointDriftSign ν : ℂ) * ζ)
  let u : ℝ≥0 := ⟨T - t, (sub_pos.mpr ht).le⟩
  let W := homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ (T - t)
    (sub_pos.mpr ht) ξ (gaussianAverage hd Q s hs g)
  let w := homogeneousAverage Q ⟨0, by omega⟩ (T - t)
    (sub_pos.mpr ht) ξ (gaussianAverage hd Q s hs g)
  let E := Real.exp (sourceReducedBound Λ * ‖ξ‖ ^ 2 * (T - t) / 2)
  have hW : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) w W :=
    homogeneousAverage_hasComplexHorizontalGradient_allData Q ⟨0, by omega⟩ (T - t)
      (sub_pos.mpr ht) ξ (gaussianAverage hd Q s hs g)
  have hsum : (∫ ω, ∑ j, J t.toNNReal j ω * W j ω ∂reducedLaw Q) =
      ∑ j, c4EndpointPairing Q (F j) (W j) := by
    rw [integral_finsetSum _ (fun j _ => integrable_complexLp_mul Q (J t.toNNReal j) (W j))]
    apply Finset.sum_congr rfl
    intro j _
    exact (c4EndpointPairing_apply Q _ _).symm.trans
      (c3EndpointPairing_centered_gradient Q w W hW _ j)
  have hdiv : ‖∫ ω, ∑ j, J t.toNNReal j ω * W j ω ∂reducedLaw Q‖ ≤
      E * (∑ j, ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) (F j)‖) * ‖g‖ := by
    rw [hsum]
    calc
      _ ≤ ∑ j, ‖c4EndpointPairing Q (F j) (W j)‖ := norm_sum_le _ _
      _ ≤ ∑ j, E * ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) (F j)‖ * ‖g‖ := by
        apply Finset.sum_le_sum
        intro j _
        exact c3EndpointPairing_homogeneousSmoothedGradient_norm_le hd Q ⟨0, by omega⟩
          ξ u (sub_pos.mpr ht) s hs (F j) g j
      _ = _ := by rw [← Finset.sum_mul, ← Finset.mul_sum]
  have hsource : (∫ ω, (J t.toNNReal ⟨0, by omega⟩ ω -
      ∫ ω', J t.toNNReal ⟨0, by omega⟩ ω' ∂reducedLaw Q) * w ω ∂reducedLaw Q) =
      c4EndpointPairing Q (F ⟨0, by omega⟩) w := by
    rw [c4EndpointPairing_apply]
    apply integral_congr_ae
    filter_upwards [coeFn_centeredComplexLp Q (J t.toNNReal ⟨0, by omega⟩)] with ω hω
    rw [hω]
  have hsrc : ‖c4EndpointPairing Q (F ⟨0, by omega⟩) w‖ ≤
      E * ‖gaussianAverage hd Q s hs (F ⟨0, by omega⟩)‖ * ‖g‖ :=
    c3EndpointPairing_homogeneousSmoothed_norm_le hd Q ⟨0, by omega⟩ ξ u
      (sub_pos.mpr ht) s hs (F ⟨0, by omega⟩) g
  rw [c3BackwardFluxFunctional, dite_eq_left ht]
  change ‖-(1 / 2 : ℂ) * (∫ ω, ∑ j, J t.toNNReal j ω * W j ω ∂reducedLaw Q) +
    c4EndpointSourceCoefficient ν ζ * (∫ ω, (J t.toNNReal ⟨0, by omega⟩ ω -
      ∫ ω', J t.toNNReal ⟨0, by omega⟩ ω' ∂reducedLaw Q) * w ω ∂reducedLaw Q)‖ ≤ _
  · rw [hsource]
    calc
      _ ≤ ‖-(1 / 2 : ℂ) * (∫ ω, ∑ j, J t.toNNReal j ω * W j ω ∂reducedLaw Q)‖ +
          ‖c4EndpointSourceCoefficient ν ζ * c4EndpointPairing Q (F ⟨0, by omega⟩) w‖ :=
        norm_add_le _ _
      _ ≤ (1 / 2 : ℝ) *
          (E * (∑ j, ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) (F j)‖) * ‖g‖) +
          ‖c4EndpointSourceCoefficient ν ζ‖ *
            (E * ‖gaussianAverage hd Q s hs (F ⟨0, by omega⟩)‖ * ‖g‖) := by
        simp only [norm_mul, norm_neg, norm_div, norm_one, Complex.norm_ofNat]
        exact add_le_add (mul_le_mul_of_nonneg_left hdiv (by norm_num))
          (mul_le_mul_of_nonneg_left hsrc (norm_nonneg _))
      _ = _ := by ring

/-- At the exponent used for duality, the vector norm in the forced-flux
proposition controls each actual reduced-L2 component. -/
theorem c3FluxVector_component_norm_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (F : Fin d → Lp ℂ 2 (reducedLaw Q)) (C : ℝ)
    (hbound : Real.sqrt (∑ j, ((eLpNorm (F j : FieldPair d → ℂ)
      (ENNReal.ofReal 2) (reducedLaw Q)).toReal) ^ 2) ≤ C) (j : Fin d) :
    ‖F j‖ ≤ C := by
  norm_num only [ENNReal.ofReal_ofNat] at hbound
  simp only [← Lp.norm_def] at hbound
  calc
    _ = Real.sqrt (‖F j‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt (∑ k, ‖F k‖ ^ 2) := Real.sqrt_le_sqrt
      (Finset.single_le_sum (fun k _ => sq_nonneg ‖F k‖) (Finset.mem_univ j))
    _ ≤ C := hbound

/-- The exact vector estimates supplied by the forced-flux proposition at p=2
control the literal physical backward functional. The source retains its
endpoint-dependent coefficient; no extra flux regularity is required. -/
theorem c3BackwardFluxFunctional_smoothed_norm_le_of_vector_bounds
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (ν : EndpointIndex d) (ζ : ℂ) (T t : ℝ) (ht : t < T)
    (J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q)) (C₀ C₁ : ℝ)
    (hzero : Real.sqrt (∑ j, ((eLpNorm
      (gaussianDerivativeAverage hd Q s hs 0 (fun j => Fin.elim0 j)
        (centeredComplexLp Q (J t.toNNReal j)) : FieldPair d → ℂ)
      (ENNReal.ofReal 2) (reducedLaw Q)).toReal) ^ 2) ≤ C₀)
    (hone : ∀ i : Fin d, Real.sqrt (∑ j, ((eLpNorm
      (gaussianDerivativeAverage hd Q s hs 1 (fun _ => i)
        (centeredComplexLp Q (J t.toNNReal j)) : FieldPair d → ℂ)
      (ENNReal.ofReal 2) (reducedLaw Q)).toReal) ^ 2) ≤ C₁) :
    ‖c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g) t‖ ≤
      Real.exp (sourceReducedBound Λ * ‖-((endpointDriftSign ν : ℂ) * ζ)‖ ^ 2 *
        (T - t) / 2) *
      ((1 / 2 : ℝ) * (d : ℝ) * C₁ + ‖c4EndpointSourceCoefficient ν ζ‖ * C₀) * ‖g‖ := by
  refine (c3BackwardFluxFunctional_smoothed_norm_le hd Q ν ζ T t ht J s hs g).trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg g)
  apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
  apply add_le_add
  · rw [mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    calc
      _ ≤ ∑ j : Fin d, C₁ := Finset.sum_le_sum fun j _ =>
        c3FluxVector_component_norm_le Q _ C₁ (hone j) j
      _ = (d : ℝ) * C₁ := by simp
  · apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    simpa only [c3GaussianDerivativeAverage_zero] using
      c3FluxVector_component_norm_le Q _ C₀ hzero ⟨0, by omega⟩

/-- Every indexed physical endpoint is one of the scalar proposition's endpoints. -/
theorem c3IndexedEndpoint_mem_collection {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (ν : EndpointIndex d) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) : indexedEndpoint hd Q ν ζ P Pdag β a μ t ∈
      endpointCollection Q ⟨0, by omega⟩ ζ P Pdag β a μ t := by
  rcases ν with i | b
  · exact Set.mem_union_left _ (Set.mem_union_right _ ⟨i, rfl⟩)
  · cases b <;> simp [indexedEndpoint, endpointCollection]

/-- At p=2 the scalar proposition controls every actual indexed endpoint,
with structural witnesses chosen before the law and observations. -/
theorem c3Scalar_indexedEndpoint_wide
    (hscalar : Blueprint.node_p_u3A_scalarStmt) {d : ℕ} (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ η C growth t₀ : ℝ, 0 < η ∧ 0 < C ∧ 0 < growth ∧ 1 ≤ t₀ ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ∀ t : ℝ≥0, t₀ ≤ (t : ℝ) → ‖ζ‖ ≤ 1 →
      ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η →
      MemLp (indexedEndpoint hd Q ν ζ P Pdag β a μ t : FieldPair d → ℂ)
        (ENNReal.ofReal 2) (reducedLaw Q) ∧
      (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ t : FieldPair d → ℂ)
        (ENNReal.ofReal 2) (reducedLaw Q)).toReal ≤
      C * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ)) *
        ((t : ℝ) ^ (-(1 / 2 + (d : ℝ) / 4)) +
          ‖ζ‖ * (t : ℝ) ^ (-(d : ℝ) / 4)) := by
  obtain ⟨a₀, η, _, _, hη, hp⟩ := hscalar d hd D
  obtain ⟨C, growth, t₀, Cder, hC, hgrowth, ht₀, _, h⟩ := hp 2 le_rfl
  refine ⟨η, C, growth, t₀, hη, hC, hgrowth, ht₀, ?_⟩
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν t ht hm hw
  exact ((h Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag).2 t ht hm hw
    _ (c3IndexedEndpoint_mem_collection hd Q ν ζ P Pdag β a μ t)).1

/-- The forward source costs at most one additional quadratic exponential
when the smoothing scale is at most the terminal time. -/
theorem c3Source_smoothing_absorption (m s T q : ℝ) (_hm : 0 ≤ m)
    (hs : 0 < s) (hsT : s ≤ T) :
    m * s ^ (-q) ≤ Real.exp (m ^ 2 * T) * s ^ (-(1 / 2 + q)) := by
  have hsq : (m * Real.sqrt s) ^ 2 = m ^ 2 * s := by
    rw [mul_pow, Real.sq_sqrt hs.le]
  have hquadratic : m * Real.sqrt s ≤ m ^ 2 * T + 1 := by
    have := mul_le_mul_of_nonneg_left hsT (sq_nonneg m)
    nlinarith [sq_nonneg (m * Real.sqrt s - 1 / 2)]
  have hexp : m * Real.sqrt s ≤ Real.exp (m ^ 2 * T) :=
    hquadratic.trans (Real.add_one_le_exp _)
  have hpower : Real.sqrt s * s ^ (-(1 / 2 + q)) = s ^ (-q) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hs]
    congr 1
    ring
  calc
    m * s ^ (-q) = (m * Real.sqrt s) * s ^ (-(1 / 2 + q)) := by rw [mul_assoc, hpower]
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp (Real.rpow_nonneg hs.le _)

/-- The two graph propositions supply physical fluxes and their actual Gaussian
bounds. Scalar input is evaluated at exactly t/8, with no added analytic premise. -/
theorem c3ForcedFlux_from_scalar
    (hscalar : Blueprint.node_p_u3A_scalarStmt)
    (hforced : Blueprint.node_l_u3A_forced_u2D_fluxStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ ε η growth t₀ : ℝ, ∃ Cder : ℕ → ℝ, ∃ L : ℕ → ℕ,
      0 < ε ∧ 0 < η ∧ η ≤ 1 / 4 ∧ 0 < growth ∧ 8 ≤ t₀ ∧
      (∀ k, 0 < Cder k) ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (hQ : HasSmoothBounds D Q)
        (β : Fin d → Lp ℂ 2 (reducedLaw Q))
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → ∀ ζ : ℂ,
      ∀ P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P →
      IsComplexTransposeSemigroup Q P Pdag → ∀ ν : EndpointIndex d,
      ∃ G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
        (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t)) ∧
      ∀ t : ℝ≥0, t₀ ≤ (t : ℝ) → ‖ζ‖ ≤ 1 →
      ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ η →
      ‖ζ‖ * Real.sqrt ((t : ℝ) / 8) ≤ ((t : ℝ) / 8) ^ η →
      ∀ s : ℝ, 1 ≤ s → ∀ hs : 0 < s, ∀ k : ℕ, ∀ dirs : Fin k → Fin d,
      Real.sqrt (∑ j, ((eLpNorm
        (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J t j)) :
          FieldPair d → ℂ) (ENNReal.ofReal 2) (reducedLaw Q)).toReal) ^ 2) ≤
        Cder k * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 2) *
          (t : ℝ) ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) *
            (1 + (t : ℝ) / s) ^ L k := by
  obtain ⟨ηs, Cs, gs, ts, hηs, hCs, hgs, hts, hs⟩ :=
    c3Scalar_indexedEndpoint_wide hscalar hd D
  obtain ⟨ε, ηf, L, hε, hηf, hp⟩ := hforced d hd D
  obtain ⟨gf, tf, Cf, hgf, htf, hCf, hf, _⟩ := hp 2 le_rfl
  let η := min (min ηs ηf) (1 / 4)
  let growth := max gs gf
  let K := max 1 Cs
  let t₀ := max tf (8 * ts)
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨ε, η, growth, t₀, (fun k => Cf k * K), L, hε,
    lt_min (lt_min hηs hηf) (by norm_num), min_le_right _ _,
    hgs.trans_le (le_max_left _ _), ?_, (fun k => mul_pos (hCf k) hK), ?_⟩
  · exact le_trans (by linarith) (le_max_right _ _)
  intro Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  obtain ⟨G, J, hflux, hbound⟩ := hf Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν
  refine ⟨G, J, hflux, ?_⟩
  intro t ht hm hw hw8 s hs1 hspos k dirs
  have htt : tf ≤ (t : ℝ) := (le_max_left _ _).trans ht
  have hts8 : ts ≤ (t : ℝ) / 8 := by
    have := (le_max_right tf (8 * ts)).trans ht
    linarith
  have ht1 : 1 ≤ (t : ℝ) := le_trans (by linarith) ((le_max_right tf (8 * ts)).trans ht)
  have ht81 : 1 ≤ (t : ℝ) / 8 := hts.trans hts8
  have hwf : ‖ζ‖ * Real.sqrt (t : ℝ) ≤ (t : ℝ) ^ ηf := hw.trans
    (Real.rpow_le_rpow_of_exponent_le ht1
      ((min_le_left _ _).trans (min_le_right _ _)))
  have hws : ‖ζ‖ * Real.sqrt ((t : ℝ) / 8) ≤ ((t : ℝ) / 8) ^ ηs := hw8.trans
    (Real.rpow_le_rpow_of_exponent_le ht81
      ((min_le_left _ _).trans (min_le_left _ _)))
  have hsmall := hs Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν (t / 8)
    (by simpa using hts8) hm (by simpa using hws)
  have hscalarBound :
      (eLpNorm (indexedEndpoint hd Q ν ζ P Pdag β a μ (t / 8) : FieldPair d → ℂ)
        (ENNReal.ofReal 2) (reducedLaw Q)).toReal ≤
      K * Real.exp (growth * ‖ζ‖ ^ 2 * (t : ℝ) / 8) *
        (((t : ℝ) / 8) ^ (-(1 / 2 + (d : ℝ) / 4)) +
          ‖ζ‖ * ((t : ℝ) / 8) ^ (-(d : ℝ) / 4)) := by
    refine hsmall.2.trans ?_
    simp only [NNReal.coe_div, NNReal.coe_ofNat]
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    apply mul_le_mul (le_max_right 1 Cs) _ (Real.exp_pos _).le (le_of_lt hK)
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right (le_max_left gs gf)
      (mul_nonneg (sq_nonneg ‖ζ‖) (show 0 ≤ (t : ℝ) from t.property))
    dsimp only [growth]
    nlinarith
  have hb := (hbound t htt hwf growth K (le_max_right _ _) (le_max_left _ _)
    hsmall.1 hscalarBound s hs1 hspos k dirs).2
  simpa only [mul_assoc] using hb


/-- A single structural terminal threshold puts both prescribed force windows
inside every earlier positive wide window, including the scalar time t/8. -/
theorem c3Late_force_windows (η δ t₀ C₀ : ℝ) (hη : 0 < η) (hηhalf : η ≤ 1 / 2)
    (hδ : 0 < δ) (hδ1 : δ < 1) (hC₀ : 0 < C₀) :
    ∃ T₀ : ℝ, 2 ≤ T₀ ∧ ∀ T : ℝ, T₀ ≤ T →
      t₀ ≤ T ^ (1 - δ) ∧ T ^ (1 - δ) ≤ T / 2 ∧
      ∀ m : ℝ, 0 ≤ m →
      (m * Real.sqrt T ≤ 2 ∨ m * Real.sqrt T ≤ C₀ * Real.log T ^ (1 / 4 : ℝ)) →
      m ≤ 1 ∧ ∀ r : ℝ, 0 < r → r ≤ T → m * Real.sqrt r ≤ r ^ η := by
  have hlog := (isLittleO_log_rpow_rpow_atTop (1 / 4 : ℝ) hη).bound
    (div_pos zero_lt_one hC₀)
  have hevent : ∀ᶠ T : ℝ in Filter.atTop,
      2 ≤ T ∧ t₀ ≤ T ^ (1 - δ) ∧ 2 ≤ T ^ δ ∧ 2 ≤ T ^ η ∧
        C₀ * Real.log T ^ (1 / 4 : ℝ) ≤ T ^ η := by
    filter_upwards [Filter.eventually_ge_atTop (2 : ℝ),
      (tendsto_rpow_atTop (by linarith : 0 < 1 - δ)).eventually_ge_atTop t₀,
      (tendsto_rpow_atTop hδ).eventually_ge_atTop 2,
      (tendsto_rpow_atTop hη).eventually_ge_atTop 2, hlog]
      with T hT ht hpowδ hpowη hl
    refine ⟨hT, ht, hpowδ, hpowη, ?_⟩
    have hT0 : 0 ≤ T := by linarith
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (Real.log_nonneg (by linarith)) _),
      Real.norm_of_nonneg (Real.rpow_nonneg hT0 _)] at hl
    have := mul_le_mul_of_nonneg_left hl hC₀.le
    simpa only [← mul_assoc, mul_one_div_cancel hC₀.ne', one_mul] using this
  obtain ⟨T₁, hT₁⟩ := Filter.eventually_atTop.1 hevent
  refine ⟨max 2 T₁, le_max_left _ _, ?_⟩
  intro T ht
  obtain ⟨hT2, hτ, hδpow, hηpow, hlogpow⟩ := hT₁ T ((le_max_right _ _).trans ht)
  have hT : 0 < T := by linarith
  have hsplit : T ^ (1 - δ) * T ^ δ = T := by
    rw [← Real.rpow_add hT]
    ring_nf
    exact Real.rpow_one T
  refine ⟨hτ, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left hδpow (Real.rpow_nonneg hT.le (1 - δ))
    rw [hsplit] at this
    linarith
  intro m hm hw
  have hterminal : m * Real.sqrt T ≤ T ^ η := hw.elim
    (fun h => h.trans hηpow) (fun h => h.trans hlogpow)
  have hsqrt : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hsmall : T ^ η ≤ Real.sqrt T := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith) hηhalf
  refine ⟨?_, fun r hr hrT => scalar_force_window_mono m r T η hm hr hrT hηhalf hterminal⟩
  nlinarith [hterminal.trans hsmall]

/-- The source term and the backward homogeneous growth fit a single terminal
Gaussian bound. The polynomial factors remain explicit and nonnegative. -/
theorem c3Flux_weight_normalize (B growth m t T s q w A₀ A₁ P₀ P₁ P : ℝ)
    (hB : 0 ≤ B) (hgrowth : 0 ≤ growth) (hm : 0 ≤ m)
    (ht : 0 ≤ t) (htT : t ≤ T) (hs : 0 < s) (hsT : s ≤ T)
    (hw : 0 ≤ w) (hA₀ : 0 ≤ A₀) (hA₁ : 0 ≤ A₁)
    (hP₀ : 0 ≤ P₀) (hP₁ : 0 ≤ P₁) (hP₀P : P₀ ≤ P) (hP₁P : P₁ ≤ P) :
    Real.exp (B * m ^ 2 * (T - t) / 2) *
      (A₁ * Real.exp (growth * m ^ 2 * t / 2) * w * s ^ (-(1 / 2 + q)) * P₁ +
        m * A₀ * Real.exp (growth * m ^ 2 * t / 2) * w * s ^ (-q) * P₀) ≤
      (A₁ + A₀) * Real.exp ((B + growth + 1) * m ^ 2 * T) *
        w * s ^ (-(1 / 2 + q)) * P := by
  have hT : 0 ≤ T := ht.trans htT
  have hP : 0 ≤ P := hP₀.trans hP₀P
  have hsource := c3Source_smoothing_absorption m s T q hm hs hsT
  have hE : Real.exp (B * m ^ 2 * (T - t) / 2) *
      Real.exp (growth * m ^ 2 * t / 2) * Real.exp (m ^ 2 * T) ≤
      Real.exp ((B + growth + 1) * m ^ 2 * T) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hBt := mul_le_mul_of_nonneg_left (show T - t ≤ 2 * T by linarith)
      (mul_nonneg hB (sq_nonneg m))
    have hgt := mul_le_mul_of_nonneg_left (show t ≤ 2 * T by linarith)
      (mul_nonneg hgrowth (sq_nonneg m))
    nlinarith only [hBt, hgt]
  have hE' : Real.exp (B * m ^ 2 * (T - t) / 2) *
      Real.exp (growth * m ^ 2 * t / 2) ≤
      Real.exp ((B + growth + 1) * m ^ 2 * T) := by
    calc
      _ ≤ Real.exp (B * m ^ 2 * (T - t) / 2) *
          Real.exp (growth * m ^ 2 * t / 2) * Real.exp (m ^ 2 * T) := by
        exact le_mul_of_one_le_right (by positivity)
          (Real.one_le_exp (mul_nonneg (sq_nonneg m) hT))
      _ ≤ _ := hE
  have hfirst : Real.exp (B * m ^ 2 * (T - t) / 2) *
      (A₁ * Real.exp (growth * m ^ 2 * t / 2) * w * s ^ (-(1 / 2 + q)) * P₁) ≤
      A₁ * Real.exp ((B + growth + 1) * m ^ 2 * T) * w *
        s ^ (-(1 / 2 + q)) * P := by
    calc
      _ = A₁ * (Real.exp (B * m ^ 2 * (T - t) / 2) *
          Real.exp (growth * m ^ 2 * t / 2)) * w * s ^ (-(1 / 2 + q)) * P₁ := by ring
      _ ≤ _ := by gcongr
  have hsecond : Real.exp (B * m ^ 2 * (T - t) / 2) *
      (m * A₀ * Real.exp (growth * m ^ 2 * t / 2) * w * s ^ (-q) * P₀) ≤
      A₀ * Real.exp ((B + growth + 1) * m ^ 2 * T) * w *
        s ^ (-(1 / 2 + q)) * P := by
    calc
      _ = A₀ * (Real.exp (B * m ^ 2 * (T - t) / 2) *
          Real.exp (growth * m ^ 2 * t / 2)) * w * (m * s ^ (-q)) * P₀ := by ring
      _ ≤ A₀ * (Real.exp (B * m ^ 2 * (T - t) / 2) *
          Real.exp (growth * m ^ 2 * t / 2)) * w *
          (Real.exp (m ^ 2 * T) * s ^ (-(1 / 2 + q))) * P := by gcongr
      _ = A₀ * (Real.exp (B * m ^ 2 * (T - t) / 2) *
          Real.exp (growth * m ^ 2 * t / 2) * Real.exp (m ^ 2 * T)) * w *
          s ^ (-(1 / 2 + q)) * P := by ring
      _ ≤ _ := by gcongr
  rw [mul_add]
  exact (add_le_add hfirst hsecond).trans_eq (by ring)

/-- Normalization of the actual k=0,1 forced-flux bounds gives the integrable
time decay needed by the physical variation formula. -/
theorem c3BackwardFluxFunctional_decay_of_gaussian_bounds
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (ν : EndpointIndex d) (ζ : ℂ) (T t : ℝ) (ht : 0 ≤ t) (htT : t < T)
    (J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (s : ℝ) (hs : 0 < s) (hsT : s ≤ T) (g : Lp ℂ 2 (reducedLaw Q))
    (ε growth : ℝ) (hgrowth : 0 ≤ growth) (Cder : ℕ → ℝ)
    (hCder : ∀ k, 0 ≤ Cder k) (L : ℕ → ℕ)
    (hbound : ∀ k : ℕ, ∀ dirs : Fin k → Fin d,
      Real.sqrt (∑ j, ((eLpNorm
        (gaussianDerivativeAverage hd Q s hs k dirs (centeredComplexLp Q (J t.toNNReal j)) :
          FieldPair d → ℂ) (ENNReal.ofReal 2) (reducedLaw Q)).toReal) ^ 2) ≤
        Cder k * Real.exp (growth * ‖ζ‖ ^ 2 * t / 2) *
          t ^ (-1 - ε) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2) * (1 + t / s) ^ L k) :
    ‖c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g) t‖ ≤
      ((1 / 2 : ℝ) * (d : ℝ) * Cder 1 + Cder 0) *
        Real.exp ((max 0 (sourceReducedBound Λ) + growth + 1) * ‖ζ‖ ^ 2 * T) *
        t ^ (-1 - ε) * s ^ (-(1 / 2 + (d : ℝ) / 4)) *
        (1 + T / s) ^ max (L 0) (L 1) * ‖g‖ := by
  let C₀ := Cder 0 * Real.exp (growth * ‖ζ‖ ^ 2 * t / 2) *
    t ^ (-1 - ε) * s ^ (-(d : ℝ) / 4) * (1 + t / s) ^ L 0
  let C₁ := Cder 1 * Real.exp (growth * ‖ζ‖ ^ 2 * t / 2) *
    t ^ (-1 - ε) * s ^ (-(1 / 2 + (d : ℝ) / 4)) * (1 + t / s) ^ L 1
  have hzero := hbound 0 (fun j => Fin.elim0 j)
  have hone := fun i : Fin d => hbound 1 (fun _ => i)
  norm_num only [Nat.cast_zero, Nat.cast_one, zero_div, sub_zero] at hzero hone
  have hCder₀ := hCder 0
  have hCder₁ := hCder 1
  have hC₀ : 0 ≤ C₀ := by dsimp [C₀]; positivity
  have hC₁ : 0 ≤ C₁ := by dsimp [C₁]; positivity
  have hsign : ‖-((endpointDriftSign ν : ℂ) * ζ)‖ = ‖ζ‖ := by
    rcases ν with j | b
    · simp [endpointDriftSign]
    · cases b <;> simp [endpointDriftSign]
  have hsource : ‖c4EndpointSourceCoefficient ν ζ‖ ≤ ‖ζ‖ := by
    rcases ν with j | b
    · simp [c4EndpointSourceCoefficient]
    · cases b <;> simp [c4EndpointSourceCoefficient]
  have hb := c3BackwardFluxFunctional_smoothed_norm_le_of_vector_bounds
    hd Q ν ζ T t htT J s hs g C₀ C₁ (by simpa [C₀] using hzero)
    (by intro i; simpa [C₁, sub_eq_add_neg, neg_div, add_comm, add_left_comm, add_assoc] using hone i)
  rw [hsign] at hb
  have hpoly : ∀ k, L k ≤ max (L 0) (L 1) →
      (1 + t / s) ^ L k ≤ (1 + T / s) ^ max (L 0) (L 1) := by
    intro k hk
    exact (pow_le_pow_left₀ (by positivity : 0 ≤ 1 + t / s)
      (by gcongr) _).trans (pow_le_pow_right₀ (le_add_of_nonneg_right (div_nonneg (ht.trans htT.le) hs.le)) hk)
  have hn := c3Flux_weight_normalize (max 0 (sourceReducedBound Λ)) growth ‖ζ‖ t T s
    ((d : ℝ) / 4) (t ^ (-1 - ε)) (Cder 0) ((1 / 2 : ℝ) * (d : ℝ) * Cder 1)
    ((1 + t / s) ^ L 0) ((1 + t / s) ^ L 1)
    ((1 + T / s) ^ max (L 0) (L 1)) (le_max_left _ _) hgrowth (norm_nonneg _)
    ht htT.le hs hsT (Real.rpow_nonneg ht _) (hCder 0) (by positivity)
    (by positivity) (by positivity) (hpoly 0 (le_max_left _ _)) (hpoly 1 (le_max_right _ _))
  refine hb.trans ?_
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  calc
    _ ≤ Real.exp (max 0 (sourceReducedBound Λ) * ‖ζ‖ ^ 2 * (T - t) / 2) *
        ((1 / 2 : ℝ) * (d : ℝ) * C₁ + ‖ζ‖ * C₀) := by
      apply mul_le_mul
      · apply Real.exp_le_exp.mpr
        exact div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _))
            (sub_nonneg.mpr htT.le)) (by norm_num)
      · gcongr
      · positivity
      · positivity
    _ ≤ _ := by simpa only [C₀, C₁, mul_assoc, neg_div] using hn

/-- At the prescribed smoothing scale, the polynomial loss is exactly the
terminal power appearing in the smoothed Duhamel statement. -/
theorem c3Smoothing_weight_scale (T b h : ℝ) (N : ℕ) (hT : 1 < T) (hb : 0 ≤ b) :
    (T ^ (1 - b)) ^ (-h) * (1 + T / T ^ (1 - b)) ^ N ≤
      (2 : ℝ) ^ N * T ^ (-h) * T ^ (b * (h + (N : ℝ))) := by
  have hT0 : 0 < T := by linarith
  have hquot : T / T ^ (1 - b) = T ^ b := by
    calc
      _ = T ^ (1 : ℝ) / T ^ (1 - b) := by rw [Real.rpow_one]
      _ = T ^ ((1 : ℝ) - (1 - b)) := (Real.rpow_sub hT0 _ _).symm
      _ = T ^ b := by congr 1; ring
  have hpow : 1 ≤ T ^ b := Real.one_le_rpow hT.le hb
  rw [hquot]
  calc
    _ ≤ (T ^ (1 - b)) ^ (-h) * (2 * T ^ b) ^ N := by
      gcongr
      linarith
    _ = (2 : ℝ) ^ N * T ^ (-h) * T ^ (b * (h + (N : ℝ))) := by
      rw [mul_pow, ← Real.rpow_natCast (T ^ b) N, ← Real.rpow_mul hT0.le,
        ← Real.rpow_mul hT0.le]
      rw [mul_left_comm _ ((2 : ℝ) ^ N), mul_assoc,
        ← Real.rpow_add hT0, ← Real.rpow_add hT0]
      congr 2
      ring

section PhysicalVariation
variable (hc : Blueprint.node_e_u3A_centered_u2D_equationsStmt)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (β : Fin d → Lp ℂ 2 (reducedLaw Q))
    (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q))
    (hβ : IsReducedDriftObservation Q hQ β) (ha : IsReducedCoefficientObservation Q a)
    (hμ : IsReducedClockObservation Q μ) (ζ : ℂ)
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) (ν : EndpointIndex d)
    (G J : ℝ≥0 → Fin d → Lp ℂ 2 (reducedLaw Q))
    (hflux : ∀ t : ℝ≥0, 0 < (t : ℝ) → IsEndpointWeakFlux hd Q ν ζ a
      (indexedEndpoint hd Q ν ζ P Pdag β a μ t) (G t) (J t))

include hc hQ hβ ha hμ hP hPdag hflux

/-- Uniqueness identifies any physical flux family with the stationary bridge.
No measurability assumption on the choice of that family is used. -/
theorem c3CenteredEndpoint_backward_flux_hasDerivAt
    (g : Lp ℂ 2 (reducedLaw Q)) (T t : ℝ) (ht : 0 < t) (htT : t < T) :
    HasDerivAt (fun u : ℝ => c4EndpointPairing Q
      (indexedEndpoint hd Q ν ζ P Pdag β a μ u.toNNReal)
      (homogeneousGaussianEvolution Q ⟨0, by omega⟩
        (-((endpointDriftSign ν : ℂ) * ζ)) (T - u).toNNReal g))
      (c3BackwardFluxFunctional hd Q ν ζ T J g t) t := by
  obtain ⟨G', J', h', hder⟩ := c3CenteredEndpoint_backwardL2_hasDerivAt
    hc hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν g T t ht htT
  have hJ := (endpointWeakFlux_unique hd h'
    (hflux t.toNNReal (by simpa only [Real.coe_toNNReal t ht.le] using ht))).2
  simpa only [c3BackwardFluxFunctional, dite_eq_left htT, hJ] using hder

/-- An integrable scalar majorant suffices for the actual physical variation
identity. Measurability of the time flux is derived from its equality to the
measurable scalar derivative, rather than imposed on the chosen flux family.
The decay estimates must supply the majorant when this lemma is used. -/
theorem c3SmoothedEndpoint_variation_of_flux_bound
    (s : ℝ) (hs : 0 < s) (T τ : ℝ) (hτ : 0 < τ) (hτT : τ < T)
    (g : Lp ℂ 2 (reducedLaw Q)) (B : ℝ → ℝ)
    (hBi : IntervalIntegrable B volume τ T)
    (hB : ∀ t ∈ Set.Ioo τ T,
      ‖c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g) t‖ ≤ B t) :
    IntervalIntegrable
      (c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g)) volume τ T ∧
    c4EndpointPairing Q (gaussianAverage hd Q s hs
      (indexedEndpoint hd Q ν ζ P Pdag β a μ T.toNNReal -
        homogeneousAverage Q ⟨0, by omega⟩ (T - τ) (sub_pos.mpr hτT)
          ((endpointDriftSign ν : ℂ) * ζ)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ τ.toNNReal))) g =
      ∫ t in τ..T, c3BackwardFluxFunctional hd Q ν ζ T J
        (gaussianAverage hd Q s hs g) t := by
  let q := gaussianAverage hd Q s hs g
  let F := fun t : ℝ => c4EndpointPairing Q
    (indexedEndpoint hd Q ν ζ P Pdag β a μ t.toNNReal)
    (homogeneousGaussianEvolution Q ⟨0, by omega⟩
      (-((endpointDriftSign ν : ℂ) * ζ)) (T - t).toNNReal q)
  let Φ := c3BackwardFluxFunctional hd Q ν ζ T J q
  have hdF (t : ℝ) (ht : t ∈ Set.Ioo τ T) : HasDerivAt F (Φ t) t :=
    c3CenteredEndpoint_backward_flux_hasDerivAt hc hd D Q hQ β a μ hβ ha hμ
      ζ P Pdag hP hPdag ν G J hflux q T t (lt_trans hτ ht.1) ht.2
  have heq : Set.EqOn (deriv F) Φ (Set.Ioo τ T) :=
    fun t ht => (hdF t ht).deriv
  have hbound : ∀ᵐ t ∂volume.restrict (Set.uIoc τ T), ‖deriv F t‖ ≤ B t := by
    rw [Set.uIoc_of_le hτT.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc,
      ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall fun t ht => by rw [heq ht]; exact hB t ht
  have hdi : IntervalIntegrable (deriv F) volume τ T :=
    hBi.mono_fun' (aestronglyMeasurable_deriv F _) hbound
  have hΦi : IntervalIntegrable Φ volume τ T := hdi.congr_uIoo (by
    simpa only [Set.uIoo_of_le hτT.le] using heq)
  have hleft : ContinuousAt F τ := by
    have hu := (c4IndexedEndpoint_differentiableAt hc hd D Q hQ β a μ hβ ha hμ
      ζ P Pdag hP hPdag ν τ hτ).continuousAt
    have hv : ContinuousAt (fun t : ℝ => homogeneousGaussianEvolution Q ⟨0, by omega⟩
        (-((endpointDriftSign ν : ℂ) * ζ)) (T - t).toNNReal q) τ :=
      ((continuous_homogeneousGaussianEvolution Q ⟨0, by omega⟩
        (-((endpointDriftSign ν : ℂ) * ζ)) q).comp
        (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))).continuousAt
    exact ((c4EndpointPairing Q).continuous.continuousAt.comp hu).clm_apply hv
  have hright : Filter.Tendsto F (nhds T) (nhds (F T)) := by
    simpa only [F, sub_self, Real.toNNReal_zero, homogeneousGaussianEvolution_zero,
      ContinuousLinearMap.id_apply] using
      c3CenteredEndpoint_backward_terminal hc hd D Q hQ β a μ hβ ha hμ
        ζ P Pdag hP hPdag ν q T (lt_trans hτ hτT)
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hτT
    hdF hΦi hleft.continuousWithinAt (hright.mono_left nhdsWithin_le_nhds)
  refine ⟨hΦi, ?_⟩
  rw [c4SmoothedEndpoint_boundary hd Q ν ζ P Pdag β a μ s hs T τ hτT g]
  exact hFTC.symm

/-- Quantitative physical Duhamel variation from the actual flux decay.
Only a pointwise decay estimate remains to be supplied by the graph decay
propositions; time measurability and integrability are conclusions. -/
theorem c3SmoothedEndpoint_variation_of_flux_decay
    (s : ℝ) (hs : 0 < s) (T τ : ℝ) (hτ : 0 < τ) (hτT : τ < T)
    (g : Lp ℂ 2 (reducedLaw Q)) (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε)
    (hdecay : ∀ t ∈ Set.Ioo τ T,
      ‖c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g) t‖ ≤
        A * t ^ (-1 - ε)) :
    let Φ := c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g)
    let error := c4EndpointPairing Q (gaussianAverage hd Q s hs
      (indexedEndpoint hd Q ν ζ P Pdag β a μ T.toNNReal -
        homogeneousAverage Q ⟨0, by omega⟩ (T - τ) (sub_pos.mpr hτT)
          ((endpointDriftSign ν : ℂ) * ζ)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ τ.toNNReal))) g
    IntervalIntegrable Φ volume τ T ∧ error = ∫ t in τ..T, Φ t ∧
      ‖error‖ ≤ A * (τ ^ (-ε) / ε) := by
  dsimp only
  have hzero : (0 : ℝ) ∉ Set.uIcc τ T := by
    rw [Set.uIcc_of_le hτT.le]
    exact fun h => (not_le_of_gt hτ) h.1
  have hpow : IntervalIntegrable (fun t : ℝ => t ^ (-1 - ε)) volume τ T :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
  have hBi := hpow.const_mul A
  obtain ⟨hΦi, hvar⟩ := c3SmoothedEndpoint_variation_of_flux_bound
    hc hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux
    s hs T τ hτ hτT g (fun t => A * t ^ (-1 - ε)) hBi hdecay
  refine ⟨hΦi, hvar, ?_⟩
  rw [hvar]
  calc
    _ ≤ ∫ t in τ..T, A * t ^ (-1 - ε) := by
      apply intervalIntegral.norm_integral_le_of_norm_le hτT.le _ hBi
      filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ T from volume.ae_ne T] with t ht hmem
      exact hdecay t ⟨hmem.1, lt_of_le_of_ne hmem.2 ht⟩
    _ = A * (∫ t in τ..T, t ^ (-1 - ε)) := intervalIntegral.integral_const_mul _ _
    _ ≤ A * (τ ^ (-ε) / ε) := mul_le_mul_of_nonneg_left
      (c4LateFlux_tail_integral hε hτ hτT.le) hA

/-- Uniform testing of the physical flux decay gives the actual smoothed L2
endpoint error. Integrability, variation and dual norm detection are discharged
inside this lemma, rather than imposed as additional reduction premises. -/
theorem c3SmoothedEndpoint_norm_of_flux_decay
    (s : ℝ) (hs : 0 < s) (T τ : ℝ) (hτ : 0 < τ) (hτT : τ < T)
    (A ε : ℝ) (hA : 0 ≤ A) (hε : 0 < ε)
    (hdecay : ∀ g : Lp ℂ 2 (reducedLaw Q), ∀ t ∈ Set.Ioo τ T,
      ‖c3BackwardFluxFunctional hd Q ν ζ T J (gaussianAverage hd Q s hs g) t‖ ≤
        A * t ^ (-1 - ε) * ‖g‖) :
    ‖gaussianAverage hd Q s hs
      (indexedEndpoint hd Q ν ζ P Pdag β a μ T.toNNReal -
        homogeneousAverage Q ⟨0, by omega⟩ (T - τ) (sub_pos.mpr hτT)
          ((endpointDriftSign ν : ℂ) * ζ)
          (indexedEndpoint hd Q ν ζ P Pdag β a μ τ.toNNReal))‖ ≤
      A * (τ ^ (-ε) / ε) := by
  apply c3Norm_le_of_endpointPairing_bound Q _
    (mul_nonneg hA (div_nonneg (Real.rpow_nonneg hτ.le _) hε.le))
  intro g
  obtain ⟨_, _, hbound⟩ := c3SmoothedEndpoint_variation_of_flux_decay
    hc hd D Q hQ β a μ hβ ha hμ ζ P Pdag hP hPdag ν G J hflux
    s hs T τ hτ hτT g (A * ‖g‖) ε (mul_nonneg hA (norm_nonneg _)) hε
    (fun t ht => by simpa only [mul_right_comm A ‖g‖] using hdecay g t ht)
  simpa only [mul_right_comm A ‖g‖] using hbound

end PhysicalVariation
end EinsteinFull
