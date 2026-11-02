import EinsteinFull.Blueprint.Foundation.Proofs.W2CenteredEquations
import EinsteinFull.Calculus.C1ClockAnalyticitySupport
import EinsteinFull.Calculus.C3SmoothedDuhamelClosureSupport

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- The actual unforced centered clock paired with a backward homogeneous test
has derivative equal to its anisotropic coefficient-defect flux. -/
theorem clock_unforced_backward_flux_hasDerivAt
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (g : Lp ℂ 2 (reducedLaw Q)) (T t : ℝ) (ht : 0 < t) (htT : t < T)
    : let J := fun (r : ℝ≥0) (j : Fin d) =>
      ClockAnalyticity.flux Q (fun k => hP.gradientOrbit μ (r : ℝ) k) j
    HasDerivAt (fun u : ℝ => c4EndpointPairing Q
      (centeredComplexLp Q (P u.toNNReal μ))
      (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 (T-u).toNNReal g))
      (c3BackwardFluxFunctional hd Q (.inr false) 0 T J g t) t := by
  classical
  have hdefect
      (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (ha : IsReducedCoefficientObservation Q a)
      (f g : Lp ℂ 2 (reducedLaw Q))
      (hfg : IsComplexGeneratorPair Q ⟨0, by omega⟩ 0 f g)
      (G J : Fin d → Lp ℂ 2 (reducedLaw Q))
      (hflux : IsEndpointWeakFlux hd Q (.inr false) 0 a (centeredComplexLp Q f) G J)
      (q : Lp ℂ 2 (reducedLaw Q)) (s : ℝ) (hs : 0 < s) :
      c4EndpointPairing Q g (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 q) -
        c4EndpointPairing Q (centeredComplexLp Q f)
          (homogeneousGaussianEvolutionTimeDerivative Q ⟨0, by omega⟩ 0 q s) =
        -(1/2 : ℂ) * (∫ ω, ∑ j, J j ω *
          homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ s hs 0 q j ω
          ∂reducedLaw Q) := by
    classical
    let v := homogeneousAverage Q ⟨0, by omega⟩ s hs 0 q
    let W := homogeneousGaussianHorizontalGradient Q ⟨0, by omega⟩ s hs 0 q
    have hW : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) v W :=
      homogeneousAverage_hasComplexHorizontalGradient_allData Q ⟨0, by omega⟩ s hs 0 q
    obtain ⟨H, hH, hw⟩ := hfg
    have hHG : H = G := hH.centered.unique hflux.1
    subst H
    have hweak := hw v W hW
    simp only [zero_mul, add_zero] at hweak
    have hgauss := c3GaussianTimeDerivative_negativeForce_weak Q ⟨0, by omega⟩
      s hs 0 (centeredComplexLp Q f) G hflux.1 q
    simp only [neg_zero, zero_mul, sub_zero, c4EndpointPairing_apply] at hgauss
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
    change (∫ ω, centeredComplexLp Q f ω *
      homogeneousGaussianEvolutionTimeDerivative Q ⟨0, by omega⟩ 0 q s ω ∂reducedLaw Q) =
      -(1/2 : ℂ) * (∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
        (∫ ω, G j ω * W k ω ∂reducedLaw Q)) at hgauss
    rw [hsym] at hgauss
    have hraw : (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * G k ω * W j ω
        ∂reducedLaw Q) =
        ∫ ω, ∑ j, ((∑ k, (homogenizedCoefficient Q j k : ℂ) * G k ω) + J j ω) *
          W j ω ∂reducedLaw Q := by
      apply integral_congr_ae
      filter_upwards [ae_all_iff.mpr hflux.2,
        ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun k => ha j k))] with ω hJ haω
      apply Finset.sum_congr rfl
      intro j _
      rw [hJ j]
      simp only [sub_zero]
      simp_rw [haω j, sub_mul, Finset.sum_sub_distrib]
      rw [← Finset.sum_mul]
      ring
    have hprod (u v : Lp ℂ 2 (reducedLaw Q)) :
        Integrable (fun ω => u ω * v ω) (reducedLaw Q) :=
      (Lp.memLp u).integrable_mul (Lp.memLp v)
    have hsplit : (∫ ω, ∑ j,
        ((∑ k, (homogenizedCoefficient Q j k : ℂ) * G k ω) + J j ω) * W j ω
        ∂reducedLaw Q) =
        (∑ j, ∑ k, (homogenizedCoefficient Q j k : ℂ) *
          (∫ ω, G k ω * W j ω ∂reducedLaw Q)) +
        (∫ ω, ∑ j, J j ω * W j ω ∂reducedLaw Q) := by
      simp_rw [add_mul, Finset.sum_mul, Finset.sum_add_distrib]
      rw [integral_add
        (integrable_finsetSum _ fun j _ => integrable_finsetSum _ fun k _ =>
          by simpa only [mul_assoc] using
            (hprod (G k) (W j)).const_mul (homogenizedCoefficient Q j k : ℂ))
        (integrable_finsetSum _ fun j _ => hprod (J j) (W j))]
      congr 1
      rw [integral_finsetSum]
      · apply Finset.sum_congr rfl
        intro j _
        rw [integral_finsetSum]
        · apply Finset.sum_congr rfl
          intro k _
          simp_rw [mul_assoc]
          rw [integral_const_mul]
        · intro k _
          simpa only [mul_assoc] using
            (hprod (G k) (W j)).const_mul (homogenizedCoefficient Q j k : ℂ)
      · intro j _
        exact integrable_finsetSum _ fun k _ => by
          simpa only [mul_assoc] using
            (hprod (G k) (W j)).const_mul (homogenizedCoefficient Q j k : ℂ)
    rw [hraw, hsplit] at hweak
    simp only [c4EndpointPairing_apply]
    change (∫ ω, g ω * v ω ∂reducedLaw Q) -
      (∫ ω, centeredComplexLp Q f ω *
        homogeneousGaussianEvolutionTimeDerivative Q ⟨0, by omega⟩ 0 q s ω ∂reducedLaw Q) =
      -(1/2 : ℂ) * (∫ ω, ∑ j, J j ω * W j ω ∂reducedLaw Q)
    linear_combination hweak - hgauss
  obtain ⟨v, hv⟩ := centeredEquations_clock_initial_generator
    (i := ⟨0, by omega⟩) (ζ := 0) hQ hμ
  have ht' : 0 < (t.toNNReal : ℝ) := by
    simpa only [Real.coe_toNNReal t ht.le] using ht
  have horbit := hP.map_generator hv t.toNNReal
  have hc : centeredComplexLp Q (P t.toNNReal v) = P t.toNNReal v := by
    apply Lp.ext
    filter_upwards [coeFn_centeredComplexLp Q (P t.toNNReal v)] with ω hω
    simpa only [horbit.integral_eq_zero, sub_zero] using hω
  have hforward := centeredEquations_forward_hasDerivAt hP hv t.toNNReal ht'
  rw [Real.coe_toNNReal t ht.le] at hforward
  have hcenter := ((centeredComplexLpCLM Q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt
    t hforward
  change HasDerivAt (fun s : ℝ => centeredComplexLpCLM Q (P s.toNNReal μ))
    (centeredComplexLpCLM Q (P t.toNNReal v)) t at hcenter
  have hW : HasDerivAt (fun u : ℝ => centeredComplexLp Q (P u.toNNReal μ))
      (P t.toNNReal v) t := by
    simpa only [centeredComplexLpCLM_apply, hc] using hcenter
  have hder := c4BackwardGaussian_hasDerivAt Q ⟨0, by omega⟩ 0 g T t htT hW
  simp only [neg_zero] at hder
  apply hder.congr_deriv
  let G := fun k => hP.gradientOrbit μ (t.toNNReal : ℝ) k
  let J := ClockAnalyticity.flux Q G
  have hG : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t.toNNReal μ) G := by
    simpa only [G, Real.toNNReal_coe] using hP.gradientOrbit_spec μ ht'
  let a := fun j k => ((memLp_reduced_coefficient_complex Q j k).mono_exponent
    (by norm_num : (2 : ℝ≥0∞) ≤ ∞)).toLp (fun ω : FieldPair d => (ω.1 0 j k : ℂ))
  have ha : IsReducedCoefficientObservation Q a := by
    intro j k
    exact MemLp.coeFn_toLp _
  have hflux : IsEndpointWeakFlux hd Q (.inr false) 0 a
      (centeredComplexLp Q (P t.toNNReal μ)) G J := by
    refine ⟨hG.centered, fun j => ?_⟩
    simpa only [sub_zero] using ClockAnalyticity.fluxCoe a ha G j
  have he := hdefect Q a ha _ _ horbit G J hflux g (T-t) (sub_pos.mpr htT)
  rw [homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ 0 (T-t).toNNReal
    (by simpa only [Real.coe_toNNReal _ (sub_pos.mpr htT).le] using sub_pos.mpr htT)]
  simp only [Real.coe_toNNReal _ (sub_pos.mpr htT).le]
  simpa only [c3BackwardFluxFunctional, dite_eq_left htT, mul_zero, neg_zero,
    c4EndpointSourceCoefficient, zero_mul, add_zero, G, J] using he

end EinsteinFull.Blueprint
