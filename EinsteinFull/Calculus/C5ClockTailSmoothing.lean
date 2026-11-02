import EinsteinFull.Calculus.C7UnitInitializationSupport
import EinsteinFull.Calculus.C1ClockBackwardVariation
import EinsteinFull.Calculus.C8InitialDriftGaussianDecay
import EinsteinFull.Blueprint.G3.node_e_u3A_clock_u2D_average
import EinsteinFull.Calculus.ComplexSemigroupUniquenessSupport
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- The graph estimate controls the literal zero-force clock orbit and its
canonical coefficient-defect flux. The existential graph witnesses are identified
by uniqueness of the actual horizontal gradient. -/
theorem clock_unforced_averaged_flux_bounds
    (havg : node_e_u3A_clock_u2D_averageStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ ε C t₀ : ℝ, 0 < ε ∧ 0 < C ∧ 1 ≤ t₀ ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
      ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
        (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P),
      ∀ (r : ℝ≥0), t₀ ≤ (r : ℝ) → ∀ (s : ℝ) (hs : 0 < s), 2 * (r : ℝ) ≤ s →
        ‖gaussianAverage hd Q s hs (centeredComplexLp Q (P r μ))‖ ≤
          C * s ^ (-(d : ℝ) / 4) ∧
        Real.sqrt (∑ j : Fin d,
          ‖gaussianAverage hd Q s hs (centeredComplexLp Q
            (ClockAnalyticity.flux Q (fun k => hP.gradientOrbit μ (r : ℝ) k) j))‖ ^ 2) ≤
          C * (r : ℝ) ^ (-1 / 2 - ε) * s ^ (-(d : ℝ) / 4) := by
  classical
  obtain ⟨ε, C, t₀, hε, hC, ht₀, hav⟩ := havg d hd D
  refine ⟨ε, C, t₀, hε, hC, ht₀, ?_⟩
  intro Q hQ a μ ha hμ P hP
  let R := fun ζ : ℂ => if ζ = 0 then P else forcedComplexEvolution Q ⟨0, by omega⟩ ζ
  have hR : ∀ ζ, IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ ζ (R ζ) := by
    intro ζ
    by_cases hζ : ζ = 0
    · subst ζ
      simpa only [R, if_pos rfl] using hP
    · simpa only [R, if_neg hζ] using
        isComplexEnvironmentSemigroup_forcedComplexEvolution Q ⟨0, by omega⟩ ζ
  obtain ⟨G, J, hflux, hb⟩ := hav Q hQ a μ ha hμ R hR
  intro r hr s hs hrs
  have hrpos : 0 < (r : ℝ) := lt_of_lt_of_le zero_lt_one (ht₀.trans hr)
  have hf := hflux 0 r hrpos
  simp only [R, if_pos rfl] at hf
  have hG : (fun k => hP.gradientOrbit μ (r : ℝ) k) = G 0 r :=
    by
      have hg := (hP.gradientOrbit_spec μ hrpos).centered
      simp only [Real.toNNReal_coe] at hg
      exact hg.unique hf.1
  have hJ (j : Fin d) :
      ClockAnalyticity.flux Q (fun k => hP.gradientOrbit μ (r : ℝ) k) j = J 0 r j := by
    rw [hG]
    apply Lp.ext
    exact (ClockAnalyticity.fluxCoe a ha (G 0 r) j).trans
      (by simpa only [sub_zero] using (hf.2 j).symm)
  obtain ⟨hW, _, _, hJb⟩ := hb r hr s hs hrs
  have hzero := (hW 0 (by simp)).2.1
  simp only [R, if_pos rfl] at hzero
  refine ⟨hzero, ?_⟩
  simp_rw [hJ]
  exact hJb

/-- A first Gaussian derivative has the structural parabolic L2 bound. -/
theorem clock_gaussian_derivative_norm_le
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (s : ℝ) (hs : 0 < s) (j : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) f‖ ≤
      (sourceReducedBound Λ + 1) * s ^ (-(1 : ℝ) / 2) * ‖f‖ := by
  have hker : homogenizedGaussianKernel Q ⟨0, by omega⟩ s hs 0 =
      homogenizedGaussianKernel Q j s hs 0 := by
    funext x
    rw [homogenizedGaussianKernel_zero_eq_ofReal, homogenizedGaussianKernel_zero_eq_ofReal]
  have hn := norm_gaussianDerivativeAverage_le hd Q s hs 1 (fun _ => j) f
  simp only [iteratedFDeriv_one_apply] at hn
  rw [hker] at hn
  simp_rw [UnitInitialization.norm_homogenizedKernel_zero_derivative Q j hs] at hn
  exact hn.trans (mul_le_mul_of_nonneg_right
    (UnitInitialization.integral_norm_homogenizedDensity_derivative_le Q j hs) (norm_nonneg _))

/-- Put the first derivative on the outer half of the actual Gaussian operator. -/
theorem clock_gaussian_derivative_half_comp
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (s : ℝ) (hs : 0 < s) (j : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) f =
      gaussianDerivativeAverage hd Q (s/2) (half_pos hs) 1 (fun _ => j)
        (gaussianAverage hd Q (s/2) (half_pos hs) f) := by
  have hfull := UnforcedIdentification.homogeneousAverage_hasHorizontalDerivative_one Q
    ⟨0, by omega⟩ s hs 0 (fun _ : Fin 1 => j) f
  have hhalf := UnforcedIdentification.homogeneousAverage_hasHorizontalDerivative_one Q
    ⟨0, by omega⟩ (s/2) (half_pos hs) 0 (fun _ : Fin 1 => j)
      (gaussianAverage hd Q (s/2) (half_pos hs) f)
  change HasComplexHorizontalDerivative _ _ _
    (homogeneousAverage Q ⟨0, by omega⟩ (s/2) (half_pos hs) 0
      (gaussianAverage hd Q (s/2) (half_pos hs) f)) _ at hhalf
  have he := UnforcedIdentification.homogeneousAverage_half_split hd Q s hs 0 f
  simp only [mul_zero] at he
  rw [← he] at hhalf
  simpa only [homogeneousDerivativeAverage, neg_zero, gaussianDerivativeAverage] using
    hfull.unique hhalf

/-- Integrate the actual unforced clock equation against a backward Gaussian.
Time measurability of the flux is derived from the scalar derivative. -/
theorem clock_unforced_smoothed_pairing_variation
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (b τ : ℝ≥0) (hb : 0 < (b : ℝ)) (hbτ : b < τ)
    (s : ℝ) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q))
    (B : ℝ → ℝ) (hBi : IntervalIntegrable B volume (b : ℝ) (τ : ℝ))
    (hB : ∀ t ∈ Ioo (b : ℝ) (τ : ℝ),
      ‖c3BackwardFluxFunctional hd Q (.inr false) 0 (τ : ℝ)
        (fun r j => ClockAnalyticity.flux Q
          (fun k => hP.gradientOrbit μ (r : ℝ) k) j)
        (gaussianAverage hd Q s hs g) t‖ ≤ B t) :
    ‖c4EndpointPairing Q (gaussianAverage hd Q s hs
      (centeredComplexLp Q (P τ μ) - homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0
        (τ-b) (centeredComplexLp Q (P b μ)))) g‖ ≤ ∫ t in (b : ℝ)..(τ : ℝ), B t := by
  let q := gaussianAverage hd Q s hs g
  let J := fun (r : ℝ≥0) j => ClockAnalyticity.flux Q
    (fun k => hP.gradientOrbit μ (r : ℝ) k) j
  let F := fun t : ℝ => c4EndpointPairing Q
    (centeredComplexLp Q (P t.toNNReal μ))
    (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 ((τ : ℝ)-t).toNNReal q)
  let Φ := c3BackwardFluxFunctional hd Q (.inr false) 0 (τ : ℝ) J q
  have hbt : (b : ℝ) < (τ : ℝ) := by exact_mod_cast hbτ
  have hdF (t : ℝ) (ht : t ∈ Ioo (b : ℝ) (τ : ℝ)) : HasDerivAt F (Φ t) t :=
    clock_unforced_backward_flux_hasDerivAt hd D Q hQ μ hμ P hP q (τ : ℝ) t
      (hb.trans ht.1) ht.2
  have heq : EqOn (deriv F) Φ (Ioo (b : ℝ) (τ : ℝ)) := fun t ht => (hdF t ht).deriv
  have hbound : ∀ᵐ t ∂volume.restrict (uIoc (b : ℝ) (τ : ℝ)), ‖deriv F t‖ ≤ B t := by
    rw [uIoc_of_le hbt.le, ← Measure.restrict_congr_set Ioo_ae_eq_Ioc,
      ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall fun t ht => by rw [heq ht]; exact hB t ht
  have hdi := hBi.mono_fun' (aestronglyMeasurable_deriv F _) hbound
  have hΦi : IntervalIntegrable Φ volume (b : ℝ) (τ : ℝ) :=
    hdi.congr_uIoo (by simpa only [uIoo_of_le hbt.le] using heq)
  have hcW : Continuous (fun t : ℝ => centeredComplexLp Q (P t.toNNReal μ)) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 μ).comp continuous_real_toNNReal)
  have hcH : Continuous (fun t : ℝ =>
      homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 ((τ : ℝ)-t).toNNReal q) :=
    (continuous_homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 q).comp
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
  have hcF : Continuous F :=
    ((c4EndpointPairing Q).continuous.comp hcW).clm_apply hcH
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hbt
    hdF hΦi hcF.continuousAt.continuousWithinAt
    (hcF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hboundary : c4EndpointPairing Q (gaussianAverage hd Q s hs
      (centeredComplexLp Q (P τ μ) - homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0
        (τ-b) (centeredComplexLp Q (P b μ)))) g = F (τ : ℝ) - F (b : ℝ) := by
    dsimp only [F, q]
    simp only [sub_self, Real.toNNReal_zero, homogeneousGaussianEvolution_zero,
      ContinuousLinearMap.id_apply, Real.toNNReal_coe]
    change c4EndpointPairing Q (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 _) g = _
    rw [c4EndpointPairing_homogeneousAverage, neg_zero, map_sub, ContinuousLinearMap.sub_apply]
    congr 1
    have htime : ((τ : ℝ)-b).toNNReal = τ-b := by
      apply NNReal.eq
      rw [Real.coe_toNNReal _ (sub_pos.mpr hbt).le, NNReal.coe_sub hbτ.le]
    rw [htime]
    have ht : 0 < ((τ-b : ℝ≥0) : ℝ) := by
      rw [NNReal.coe_sub hbτ.le]
      exact sub_pos.mpr hbt
    simp only [homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ 0 (τ-b) ht]
    simpa only [neg_zero, gaussianAverage, homogeneousAverage] using
      c4EndpointPairing_homogeneousAverage Q ⟨0, by omega⟩ _ ht 0 _ _
  rw [hboundary, ← hFTC]
  apply intervalIntegral.norm_integral_le_of_norm_le hbt.le _ hBi
  filter_upwards [show ∀ᵐ t : ℝ ∂volume, t ≠ (τ : ℝ) from volume.ae_ne (τ : ℝ)] with t ht hmem
  exact hB t ⟨hmem.1, lt_of_le_of_ne hmem.2 ht⟩

/-- The late clock-flux majorant loses at most the square root of elapsed time. -/
theorem clock_half_power_integral {b τ : ℝ} (hb : 0 < b) (hbτ : b ≤ τ) :
    (∫ t in b..τ, t ^ (-(1 : ℝ)/2)) ≤ 2 * Real.sqrt τ := by
  have hzero : (0 : ℝ) ∉ uIcc b τ := by
    rw [uIcc_of_le hbτ]
    exact fun h => (not_le_of_gt hb) h.1
  rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
  norm_num only [show -(1 : ℝ)/2 + 1 = 1/2 by norm_num]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  nlinarith only [Real.sqrt_nonneg b]

/-- Near the parabolic boundary, the two averaged endpoint bounds suffice. -/
theorem clock_gaussian_tail_triangle
    {d : ℕ} (hd : 2 ≤ d) {Λ r : ℝ} (Q : EnvironmentLaw d Λ r)
    (s : ℝ) (hs : 0 < s) (u v : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0)
    (B : ℝ) (hu : ‖gaussianAverage hd Q s hs u‖ ≤ B)
    (hv : ‖gaussianAverage hd Q s hs v‖ ≤ B) :
    ‖gaussianAverage hd Q s hs (u - homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t v)‖ ≤
      2 * B := by
  have hcomm : gaussianAverage hd Q s hs
      (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t v) =
      homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t (gaussianAverage hd Q s hs v) := by
    simpa only [c3GaussianDerivativeAverage_zero] using
      c3GaussianDerivativeAverage_homogeneousEvolution hd Q ⟨0, by omega⟩ 0 t
        s hs 0 (fun i => Fin.elim0 i) v
  have hn : ‖homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t
      (gaussianAverage hd Q s hs v)‖ ≤ ‖gaussianAverage hd Q s hs v‖ := by
    have hb := (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t).le_opNorm
      (gaussianAverage hd Q s hs v)
    have hop := norm_homogeneousGaussianEvolution_le Q ⟨0, by omega⟩ 0 t
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      mul_zero, zero_mul, zero_div, Real.exp_zero] at hop
    exact hb.trans ((mul_le_mul_of_nonneg_right hop (norm_nonneg _)).trans_eq (one_mul _))
  change ‖homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0
    (u - homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t v)‖ ≤ _
  rw [map_sub]
  change ‖gaussianAverage hd Q s hs u - gaussianAverage hd Q s hs
    (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t v)‖ ≤ _
  rw [hcomm]
  exact (norm_sub_le _ _).trans (by linarith only [hu, hn.trans hv])

/-- Gaussian flux averaging at half the smoothing time controls the actual
clock Duhamel remainder, without any extra time measurability premise. -/
theorem clock_gaussian_tail_from_flux
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (b τ : ℝ≥0) (hb : 0 < (b : ℝ)) (hbτ : b < τ)
    (s : ℝ) (hs : 0 < s) (C : ℝ) (hC : 0 ≤ C)
    (hflux : ∀ t ∈ Ioo (b : ℝ) (τ : ℝ), ∀ j : Fin d,
      ‖gaussianAverage hd Q (s/2) (half_pos hs) (centeredComplexLp Q
        (ClockAnalyticity.flux Q (fun k => hP.gradientOrbit μ (t.toNNReal : ℝ) k) j))‖ ≤
        C * t ^ (-(1 : ℝ)/2) * (s/2) ^ (-(d : ℝ)/4)) :
    ‖gaussianAverage hd Q s hs (centeredComplexLp Q (P τ μ) -
      homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 (τ-b) (centeredComplexLp Q (P b μ)))‖ ≤
      (d : ℝ) * (sourceReducedBound D.ellipticity + 1) * C *
        ((s/2) ^ (-(1 : ℝ)/2) * (s/2) ^ (-(d : ℝ)/4)) * Real.sqrt (τ : ℝ) := by
  let K := sourceReducedBound D.ellipticity + 1
  have hK : 0 ≤ K := by
    dsimp only [K]
    have hk := Clock.sourceReducedBound_pos D.one_le_ellipticity
    linarith
  let A := (1/2 : ℝ) * (d : ℝ) * K * C *
    ((s/2) ^ (-(1 : ℝ)/2) * (s/2) ^ (-(d : ℝ)/4))
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hbt : (b : ℝ) < (τ : ℝ) := by exact_mod_cast hbτ
  have hzero : (0 : ℝ) ∉ uIcc (b : ℝ) (τ : ℝ) := by
    rw [uIcc_of_le hbt.le]
    exact fun h => (not_le_of_gt hb) h.1
  have hpow : IntervalIntegrable (fun t : ℝ => t ^ (-(1 : ℝ)/2)) volume (b : ℝ) (τ : ℝ) :=
    intervalIntegral.intervalIntegrable_rpow (Or.inr hzero)
  apply c3Norm_le_of_endpointPairing_bound Q _ (by positivity)
  intro g
  have hBi := (hpow.const_mul A).mul_const ‖g‖
  have hv := clock_unforced_smoothed_pairing_variation hd D Q hQ μ hμ P hP
    b τ hb hbτ s hs g (fun t => A * t ^ (-(1 : ℝ)/2) * ‖g‖) hBi
  have hbound : ∀ t ∈ Ioo (b : ℝ) (τ : ℝ),
      ‖c3BackwardFluxFunctional hd Q (.inr false) 0 (τ : ℝ)
        (fun r j => ClockAnalyticity.flux Q (fun k => hP.gradientOrbit μ (r : ℝ) k) j)
        (gaussianAverage hd Q s hs g) t‖ ≤ A * t ^ (-(1 : ℝ)/2) * ‖g‖ := by
    intro t ht
    let J := fun (r : ℝ≥0) j => ClockAnalyticity.flux Q (fun k => hP.gradientOrbit μ (r : ℝ) k) j
    let F := fun j => centeredComplexLp Q (J t.toNNReal j)
    have hj (j : Fin d) : ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) (F j)‖ ≤
        K * (s/2) ^ (-(1 : ℝ)/2) * (C * t ^ (-(1 : ℝ)/2) * (s/2) ^ (-(d : ℝ)/4)) := by
      rw [clock_gaussian_derivative_half_comp]
      exact (clock_gaussian_derivative_norm_le hd Q (s/2) (half_pos hs) j _).trans
        (mul_le_mul_of_nonneg_left (hflux t ht j) (by positivity))
    have hn := c3BackwardFluxFunctional_smoothed_norm_le hd Q (.inr false) 0
      (τ : ℝ) t ht.2 J s hs g
    dsimp only at hn
    simp only [mul_zero, neg_zero, norm_zero, zero_pow (by norm_num : 2 ≠ 0),
      zero_div, Real.exp_zero, c4EndpointSourceCoefficient, zero_mul, add_zero, one_mul] at hn
    apply hn.trans
    have hsum : (∑ j : Fin d, ‖gaussianDerivativeAverage hd Q s hs 1 (fun _ => j) (F j)‖) ≤
        (d : ℝ) * (K * (s/2) ^ (-(1 : ℝ)/2) *
          (C * t ^ (-(1 : ℝ)/2) * (s/2) ^ (-(d : ℝ)/4))) := by
      calc
        _ ≤ ∑ _j : Fin d, K * (s/2) ^ (-(1 : ℝ)/2) *
            (C * t ^ (-(1 : ℝ)/2) * (s/2) ^ (-(d : ℝ)/4)) := Finset.sum_le_sum fun j _ => hj j
        _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc
      _ ≤ (1/2 : ℝ) * ((d : ℝ) * (K * (s/2) ^ (-(1 : ℝ)/2) *
          (C * t ^ (-(1 : ℝ)/2) * (s/2) ^ (-(d : ℝ)/4)))) * ‖g‖ := by
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsum (by norm_num)) (norm_nonneg _)
      _ = _ := by dsimp only [A]; ring
  refine (hv hbound).trans ?_
  rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_const_mul]
  calc
    _ ≤ (A * (2 * Real.sqrt (τ : ℝ))) * ‖g‖ :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (clock_half_power_integral hb hbt.le) hA) (norm_nonneg _)
    _ = _ := by dsimp only [A, K]; ring

/-- The half-time factors have precisely the desired dimension and time scale. -/
theorem clock_tail_half_scale {d : ℕ} {s τ : ℝ} (hs : 0 < s) (hτ : 0 ≤ τ) :
    ((s/2) ^ (-(1 : ℝ)/2) * (s/2) ^ (-(d : ℝ)/4)) * Real.sqrt τ =
      (1/2 : ℝ) ^ (-(1 : ℝ)/2 - (d : ℝ)/4) *
        s ^ (-(d : ℝ)/4) * Real.sqrt (τ/s) := by
  have he : s/2 = (1/2 : ℝ) * s := by ring
  have hp : s ^ (-(1 : ℝ)/2) = (Real.sqrt s)⁻¹ := by
    rw [neg_div, Real.rpow_neg hs.le, ← Real.sqrt_eq_rpow]
  rw [he]
  simp_rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 1/2) hs.le]
  rw [sub_eq_add_neg, Real.rpow_add (by norm_num : (0 : ℝ) < 1/2),
    hp, Real.sqrt_div hτ]
  ring

/-- One component is controlled by the Euclidean norm of a finite family. -/
theorem clock_component_le_sqrt_sum {d : ℕ} (f : Fin d → ℝ)
    (hf : ∀ j, 0 ≤ f j) (j : Fin d) : f j ≤ Real.sqrt (∑ k, f k ^ 2) := by
  calc
    f j = Real.sqrt (f j ^ 2) := (Real.sqrt_sq (hf j)).symm
    _ ≤ _ := Real.sqrt_le_sqrt
      (Finset.single_le_sum (fun k _ => sq_nonneg (f k)) (Finset.mem_univ j))

/-- The tail of the actual unforced clock equation has the Gaussian smoothing rate. -/
theorem clock_tail_gaussian_smoothing
    : ∀ (havg : node_e_u3A_clock_u2D_averageStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
      ∃ C t₀ : ℝ, 0 < C ∧ 1 ≤ t₀ ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
      ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P →
      ∀ (b τ : ℝ≥0), t₀ ≤ (b : ℝ) → b ≤ τ →
      ∀ (s : ℝ) (hs : 0 < s), 2*(τ : ℝ) ≤ s →
        ‖gaussianAverage hd Q s hs (centeredComplexLp Q (P τ μ) -
          homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 (τ-b) (centeredComplexLp Q (P b μ)))‖ ≤
          C * s ^ (-(d : ℝ)/4) * ((τ : ℝ)/s + Real.sqrt ((τ : ℝ)/s)) := by
  intro havg d hd D
  obtain ⟨ε, C₀, t₀, hε, hC₀, ht₀, hav⟩ := clock_unforced_averaged_flux_bounds havg d hd D
  let K := sourceReducedBound D.ellipticity + 1
  have hK : 0 < K := by
    have hk := Clock.sourceReducedBound_pos D.one_le_ellipticity
    dsimp only [K]
    linarith
  let A := (d : ℝ) * K * C₀ * (1/2 : ℝ) ^ (-(1 : ℝ)/2 - (d : ℝ)/4)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  let C := 4 * C₀ + A + 1
  have hC : 0 < C := by dsimp only [C]; positivity
  refine ⟨C, t₀, hC, ht₀, ?_⟩
  intro Q hQ a μ ha hμ P hP b τ hb hbτ s hs hτs
  have hbpos : 0 < (b : ℝ) := lt_of_lt_of_le zero_lt_one (ht₀.trans hb)
  have hτpos : 0 < (τ : ℝ) := hbpos.trans_le (by exact_mod_cast hbτ)
  have hτ : t₀ ≤ (τ : ℝ) := hb.trans (by exact_mod_cast hbτ)
  have hbn := hav Q hQ a μ ha hμ P hP b hb s hs
    (by
      have hbt : (b : ℝ) ≤ τ := by exact_mod_cast hbτ
      linarith only [hbt, hτs])
  have hτn := hav Q hQ a μ ha hμ P hP τ hτ s hs hτs
  have hscale : 0 ≤ s ^ (-(d : ℝ)/4) := Real.rpow_nonneg hs.le _
  have hratio : 0 ≤ (τ : ℝ)/s := div_nonneg τ.coe_nonneg hs.le
  have hCnear : 4 * C₀ ≤ C := by dsimp only [C]; linarith only [hA]
  have hCfar : A ≤ C := by dsimp only [C]; linarith only [hC₀]
  by_cases hfar : 4 * (τ : ℝ) ≤ s
  · by_cases heq : b = τ
    · subst b
      simpa only [tsub_self, homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_apply,
        sub_self, gaussianAverage, map_zero, smul_zero, integral_zero, norm_zero] using
        (show 0 ≤ C * s ^ (-(d : ℝ)/4) * ((τ : ℝ)/s + Real.sqrt ((τ : ℝ)/s)) by positivity)
    have hbt : b < τ := lt_of_le_of_ne hbτ heq
    have hflux : ∀ t ∈ Ioo (b : ℝ) (τ : ℝ), ∀ j : Fin d,
        ‖gaussianAverage hd Q (s/2) (half_pos hs) (centeredComplexLp Q
          (ClockAnalyticity.flux Q (fun k => hP.gradientOrbit μ (t.toNNReal : ℝ) k) j))‖ ≤
          C₀ * t ^ (-(1 : ℝ)/2) * (s/2) ^ (-(d : ℝ)/4) := by
      intro t ht j
      have htpos : 0 < t := hbpos.trans ht.1
      have htime₀ : t₀ ≤ t := hb.trans ht.1.le
      have ht1 : 1 ≤ t := ht₀.trans htime₀
      have htr : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t htpos.le
      have hjb := (hav Q hQ a μ ha hμ P hP t.toNNReal
        (by rw [htr]; exact htime₀) (s/2) (half_pos hs)
        (by rw [htr]; linarith only [hfar, ht.2])).2
      have hj := (clock_component_le_sqrt_sum
        (fun j => ‖gaussianAverage hd Q (s/2) (half_pos hs) (centeredComplexLp Q
          (ClockAnalyticity.flux Q (fun k => hP.gradientOrbit μ (t.toNNReal : ℝ) k) j))‖)
        (fun _ => norm_nonneg _) j).trans hjb
      rw [htr] at hj
      rw [htr]
      have hp : t ^ (-1/2 - ε) ≤ t ^ (-(1 : ℝ)/2) :=
        Real.rpow_le_rpow_of_exponent_le ht1 (by linarith only [hε])
      exact hj.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp hC₀.le)
        (Real.rpow_nonneg (half_pos hs).le _))
    have hbnd := clock_gaussian_tail_from_flux hd D Q hQ μ hμ P hP b τ hbpos hbt
      s hs C₀ hC₀.le hflux
    rw [mul_assoc ((d : ℝ) * (sourceReducedBound D.ellipticity + 1) * C₀),
      clock_tail_half_scale hs τ.coe_nonneg] at hbnd
    have hfinal : ‖gaussianAverage hd Q s hs (centeredComplexLp Q (P τ μ) -
        homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 (τ-b)
          (centeredComplexLp Q (P b μ)))‖ ≤
        A * s ^ (-(d : ℝ)/4) * Real.sqrt ((τ : ℝ)/s) := by
      simpa only [A, K, mul_assoc] using hbnd
    calc
      _ ≤ A * s ^ (-(d : ℝ)/4) * Real.sqrt ((τ : ℝ)/s) := hfinal
      _ ≤ C * s ^ (-(d : ℝ)/4) * Real.sqrt ((τ : ℝ)/s) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hratio) (by positivity)
  · have hbnd := clock_gaussian_tail_triangle hd Q s hs (centeredComplexLp Q (P τ μ))
      (centeredComplexLp Q (P b μ)) (τ-b) (C₀ * s ^ (-(d : ℝ)/4)) hτn.1 hbn.1
    have hroot : (1/2 : ℝ) ≤ Real.sqrt ((τ : ℝ)/s) := by
      apply (Real.le_sqrt (by norm_num) hratio).mpr
      have hx : s < 4 * (τ : ℝ) := lt_of_not_ge hfar
      apply (le_div_iff₀ hs).mpr
      nlinarith only [hx]
    calc
      _ ≤ 2 * (C₀ * s ^ (-(d : ℝ)/4)) := hbnd
      _ ≤ (4 * C₀) * s ^ (-(d : ℝ)/4) * Real.sqrt ((τ : ℝ)/s) := by
        nlinarith only [mul_le_mul_of_nonneg_left hroot (show 0 ≤ 4*C₀*s^(-(d:ℝ)/4) by positivity)]
      _ ≤ C * s ^ (-(d : ℝ)/4) * Real.sqrt ((τ : ℝ)/s) := by gcongr
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hratio) (by positivity)

end EinsteinFull.Blueprint
