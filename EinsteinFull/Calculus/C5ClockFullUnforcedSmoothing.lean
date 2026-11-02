import EinsteinFull.Calculus.C5ClockTailSmoothing
import EinsteinFull.Calculus.C1ClockBackwardVariation
import EinsteinFull.Calculus.C5ClockDerivativeKernelDecay
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import EinsteinFull.Work.W6.SamplewiseTemporalFubiniProof
open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology MeasureTheory
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation
/-- Finite-range covariance controls a positive-time homogeneous increment of
 the literal centered clock, uniformly over the environment law. -/
theorem clock_homogeneous_increment_decay
    (d : ℕ) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ (i : Fin d) (s t : ℝ) (hs : 0 < s) (ht : 0 ≤ t),
        ‖homogeneousGaussianEvolution Q i 0 (NNReal.mk (s+t) (by positivity)) (centeredComplexLp Q μ) -
          homogeneousGaussianEvolution Q i 0 (NNReal.mk s hs.le) (centeredComplexLp Q μ)‖ ≤
          C * s ^ (-(d : ℝ)/4) * (t/s) := by
  obtain ⟨C, hC, hb⟩ := clock_gaussian_time_derivative_decay d D
  refine ⟨C, hC, ?_⟩
  intro Q hQ μ hμ i s t hs ht
  have hst : s ≤ s+t := le_add_of_nonneg_right ht
  unfold NNReal.mk
  rw [homogeneousGaussianEvolution_sub_eq_integral_timeDerivative Q i 0
    (centeredComplexLp Q μ) s (s+t) hs hst]
  have hbound (u : ℝ) (hu : u ∈ Icc s (s+t)) :
      ‖homogeneousGaussianEvolutionTimeDerivative Q i 0 (centeredComplexLp Q μ) u‖ ≤
        C * s⁻¹ * s ^ (-(d : ℝ)/4) := by
    have hu0 : 0 < u := hs.trans_le hu.1
    have hb' := hb Q hQ μ hμ i 0 u hu0
    simp only [norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
      add_zero, mul_zero, zero_mul, Real.exp_zero, mul_one] at hb'
    refine hb'.trans (mul_le_mul ?_ ?_ (Real.rpow_nonneg hu0.le _) (by positivity))
    · exact mul_le_mul_of_nonneg_left (inv_anti₀ hs hu.1) hC.le
    · exact Real.rpow_le_rpow_of_nonpos hs hu.1 (by
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        linarith only [hd0])
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := s+t)
    (fun u hu => hbound u (by simpa only [uIcc_of_le hst] using (uIoc_subset_uIcc hu)))
  have he : (C * s⁻¹ * s ^ (-(d : ℝ)/4)) * |s+t-s| =
      C * s ^ (-(d : ℝ)/4) * (t/s) := by
    rw [add_sub_cancel_left, abs_of_nonneg ht]
    ring
  exact hnorm.trans_eq he

/-- Gaussian smoothing of the homogeneous clock displacement has the
linear time-ratio term in the unforced clock estimate. -/
theorem clock_gaussian_homogeneous_displacement
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ (t : ℝ≥0) (s : ℝ) (hs : 0 < s),
        ‖gaussianAverage hd Q s hs
          (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t (centeredComplexLp Q μ) -
            centeredComplexLp Q μ)‖ ≤ C * s ^ (-(d : ℝ)/4) * ((t : ℝ)/s) := by
  obtain ⟨C, hC, hb⟩ := clock_homogeneous_increment_decay d D
  refine ⟨C, hC, ?_⟩
  intro Q hQ μ hμ t s hs
  by_cases ht : t = 0
  · subst t
    simp only [homogeneousGaussianEvolution_zero, ContinuousLinearMap.id_apply,
      sub_self, gaussianAverage, map_zero, smul_zero, integral_zero, norm_zero,
      NNReal.coe_zero, zero_div, mul_zero, le_refl]
  have htpos : 0 < (t : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr ht)
  have he := hb Q hQ μ hμ ⟨0, by omega⟩ s t hs t.coe_nonneg
  rw [homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ 0
      (NNReal.mk (s+(t : ℝ)) (by positivity)) (by simpa only [NNReal.coe_mk] using
        (show 0 < s+(t : ℝ) by positivity)),
    homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ 0 (NNReal.mk s hs.le)
      (by simpa only [NNReal.coe_mk] using hs)] at he
  change ‖homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0
    (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t (centeredComplexLp Q μ) -
      centeredComplexLp Q μ)‖ ≤ _
  rw [map_sub]
  change ‖homogeneousAverage Q ⟨0, by omega⟩ s hs 0
    (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 t (centeredComplexLp Q μ)) -
      homogeneousAverage Q ⟨0, by omega⟩ s hs 0 (centeredComplexLp Q μ)‖ ≤ _
  rw [homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ 0 t htpos,
    homogeneousAverage_add]
  exact he

/-- The literal clock itself has structural finite-range Gaussian decay. -/
theorem clock_initial_gaussian_decay
    (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
        (μ : Lp ℂ 2 (reducedLaw Q)), IsReducedClockObservation Q μ →
      ∀ (s : ℝ) (hs : 0 < s),
        ‖gaussianAverage hd Q s hs (centeredComplexLp Q μ)‖ ≤
          C * s ^ (-(d : ℝ)/4) := by
  obtain ⟨L, A, B, hL, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  have hp : Fact (1 ≤ ENNReal.ofReal (2 : ℝ)) := ⟨by norm_num⟩
  haveI := hp
  obtain ⟨C, hC, hdecay⟩ :=
    UnitInitialization.exists_gaussian_average_of_gaussian_norm_approximants
      d D.ellipticity D.dependenceRange 1 (2*L) 0 1 2
        (by norm_num) (by positivity) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C+1, by positivity, ?_⟩
  intro Q μ hμ s hs
  have hbound : ∀ᵐ ω ∂reducedLaw Q, ‖μ ω‖ ≤ L := by
    filter_upwards [hμ, (hb d D.dependenceRange Q).2.2] with ω he hω
    rw [he, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ((inv_nonneg.mpr (zero_le_one.trans hL)).trans (hω.2.1 0).1)]
    exact (hω.2.1 0).2
  have hlocal (n : ℕ) : IsComplexLocalObservation Q (1 + n) μ := by
    refine ⟨fun ω => (ω.2 0 : ℂ), ?_, hμ.symm⟩
    have hzero : (0 : Vec d) ∈ {x : Vec d | euclideanNorm x < 1 + (n : ℝ)} := by
      simp only [Set.mem_ofPred_eq, euclideanNorm, euclideanSq, dot, Pi.zero_apply,
        mul_zero, Finset.sum_const_zero, Real.sqrt_zero]
      positivity
    have heval : Measurable[localSigma {x : Vec d | euclideanNorm x < 1 + (n : ℝ)}]
        (fun ω : FieldPair d => (ω.1 0, ω.2 0)) :=
      Measurable.of_comap_le (le_iSup_of_le ⟨0, hzero⟩ le_rfl)
    exact Complex.measurable_ofReal.comp heval.snd
  have h := hdecay hd Q (Localization.finiteRange_map_reduce Q.measure Q.finiteRange)
    (centeredComplexLp Q μ) (fun _ => centeredComplexLp Q μ)
    (fun _ => UnitInitialization.ae_norm_centered_le Q μ hbound)
    (fun n => isComplexLocal_centered Q (hlocal n))
    (fun _ => integral_centeredComplexLp Q μ)
    (fun _ => by simp only [sub_self, norm_zero, zero_mul, le_refl]) s hs
  have hn : ‖gaussianAverage hd Q s hs (centeredComplexLp Q μ)‖ ≤
      C * s ^ (-(d : ℝ)/4) := by
    simpa only [Lp.norm_def, ENNReal.ofReal_ofNat] using h.2
  exact hn.trans (mul_le_mul_of_nonneg_right (by linarith : C ≤ C+1)
    (Real.rpow_nonneg hs.le _))

/-- The full unforced clock estimate in the regime where the smoothing
scale is at most four times the elapsed time. -/
theorem clock_unforced_near_gaussian_smoothing
    (havg : node_e_u3A_clock_u2D_averageStmt) (d : ℕ) (hd : 2 ≤ d)
    (D : StructuralData d) :
    ∃ C t₀ : ℝ, 0 < C ∧ 1 ≤ t₀ ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
      ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P →
      ∀ (τ : ℝ≥0), t₀ ≤ (τ : ℝ) →
      ∀ (s : ℝ) (hs : 0 < s), 2*(τ : ℝ) ≤ s → s ≤ 4*(τ : ℝ) →
        ‖gaussianAverage hd Q s hs (centeredComplexLp Q (P τ μ) -
          centeredComplexLp Q μ)‖ ≤
          C * s ^ (-(d : ℝ)/4) * ((τ : ℝ)/s + Real.sqrt ((τ : ℝ)/s)) := by
  obtain ⟨ε, C₀, t₀, _, hC₀, ht₀, hav⟩ :=
    clock_unforced_averaged_flux_bounds havg d hd D
  obtain ⟨C₁, hC₁, hinit⟩ := clock_initial_gaussian_decay d hd D
  refine ⟨2*(C₀+C₁), t₀, by positivity, ht₀, ?_⟩
  intro Q hQ a μ ha hμ P hP τ hτ s hs hτs hsτ
  have hscale : 0 ≤ s ^ (-(d : ℝ)/4) := Real.rpow_nonneg hs.le _
  have hratio : 0 ≤ (τ : ℝ)/s := div_nonneg τ.coe_nonneg hs.le
  have hroot : (1/2 : ℝ) ≤ Real.sqrt ((τ : ℝ)/s) := by
    apply (Real.le_sqrt (by norm_num) hratio).mpr
    apply (le_div_iff₀ hs).mpr
    linarith only [hsτ]
  have hb := (hav Q hQ a μ ha hμ P hP τ hτ s hs hτs).1
  have hi := hinit Q μ hμ s hs
  have htriangle : ‖gaussianAverage hd Q s hs (centeredComplexLp Q (P τ μ) -
      centeredComplexLp Q μ)‖ ≤ (C₀+C₁) * s ^ (-(d : ℝ)/4) := by
    change ‖homogeneousAverageCLM Q ⟨0, by omega⟩ s hs 0
      (centeredComplexLp Q (P τ μ) - centeredComplexLp Q μ)‖ ≤ _
    rw [map_sub]
    exact (norm_sub_le _ _).trans (by
      change ‖gaussianAverage hd Q s hs (centeredComplexLp Q (P τ μ))‖ +
        ‖gaussianAverage hd Q s hs (centeredComplexLp Q μ)‖ ≤ _
      calc
        _ ≤ C₀ * s ^ (-(d : ℝ)/4) + C₁ * s ^ (-(d : ℝ)/4) := add_le_add hb hi
        _ = _ := (add_mul _ _ _).symm)
  apply htriangle.trans
  have hm := mul_le_mul_of_nonneg_left hroot
    (show 0 ≤ 2*(C₀+C₁)*s^(-(d : ℝ)/4) by positivity)
  have hn : 0 ≤ 2*(C₀+C₁)*s^(-(d : ℝ)/4)*((τ : ℝ)/s) := by positivity
  nlinarith only [hm, hn]

/-- The literal clock weak variation starts at time zero. The canonical
flux is integrable as a scalar pairing; no time measurability premise is needed. -/
theorem clock_unforced_initial_pairing_variation
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (q : Lp ℂ 2 (reducedLaw Q)) (T b : ℝ) (hb : 0 < b) (hbT : b < T) :
    let Φ := c3BackwardFluxFunctional hd Q (.inr false) 0 T
      (fun r j => ClockAnalyticity.flux Q (fun k => hP.gradientOrbit μ (r : ℝ) k) j) q
    IntervalIntegrable Φ volume 0 b ∧
      c4EndpointPairing Q (centeredComplexLp Q (P b.toNNReal μ))
        (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 (T-b).toNNReal q) -
      c4EndpointPairing Q (centeredComplexLp Q μ)
        (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 T.toNNReal q) =
      ∫ t in (0 : ℝ)..b, Φ t := by
  dsimp only
  obtain ⟨g, hg⟩ := centeredEquations_clock_initial_generator
    (i := ⟨0, by omega⟩) (ζ := 0) hQ hμ
  let F := fun t : ℝ => c4EndpointPairing Q
    (centeredComplexLp Q (P t.toNNReal μ))
    (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 (T-t).toNNReal q)
  let Ψ := fun t : ℝ =>
    c4EndpointPairing Q (P t.toNNReal g)
      (homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 (T-t).toNNReal q) -
    c4EndpointPairing Q (centeredComplexLp Q (P t.toNNReal μ))
      (homogeneousGaussianEvolutionTimeDerivative Q ⟨0, by omega⟩ 0 q (T-t))
  have hc : Continuous (fun t : ℝ => centeredComplexLp Q (P t.toNNReal μ)) := by
    simpa only [Function.comp_def, centeredComplexLpCLM_apply] using
      (centeredComplexLpCLM Q).continuous.comp
        ((hP.2.2.1 μ).comp continuous_real_toNNReal)
  have hv : Continuous (fun t : ℝ =>
      homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 (T-t).toNNReal q) :=
    (continuous_homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 q).comp
      (continuous_real_toNNReal.comp (continuous_const.sub continuous_id))
  have hD : ContinuousOn (fun t : ℝ =>
      homogeneousGaussianEvolutionTimeDerivative Q ⟨0, by omega⟩ 0 q (T-t)) (Icc 0 b) :=
    (continuousOn_homogeneousGaussianEvolutionTimeDerivative Q ⟨0, by omega⟩ 0 q).comp
      (continuous_const.sub continuous_id).continuousOn
      (fun t ht => by change 0 < T-t; linarith [ht.2])
  have hF : Continuous F := ((c4EndpointPairing Q).continuous.comp hc).clm_apply hv
  have hΨ : ContinuousOn Ψ (Icc 0 b) :=
    (((c4EndpointPairing Q).continuous.comp
      ((hP.2.2.1 g).comp continuous_real_toNNReal)).clm_apply hv).continuousOn.sub
      (((c4EndpointPairing Q).continuous.comp hc).continuousOn.clm_apply hD)
  have hi : IntervalIntegrable Ψ volume 0 b := hΨ.intervalIntegrable_of_Icc hb.le
  have hdF (t : ℝ) (ht : t ∈ Ioo 0 b) : HasDerivAt F (Ψ t) t := by
    have hmean : (∫ ω, P t.toNNReal g ω ∂reducedLaw Q) = 0 :=
      (hP.map_generator hg t.toNNReal).integral_eq_zero
    have hcent : centeredComplexLp Q (P t.toNNReal g) = P t.toNNReal g := by
      apply Lp.ext
      filter_upwards [coeFn_centeredComplexLp Q (P t.toNNReal g)] with ω hω
      simpa only [hmean, sub_zero] using hω
    have hu := centeredEquations_forward_hasDerivAt hP hg t.toNNReal
      (by simpa only [Real.coe_toNNReal t ht.1.le] using ht.1)
    rw [Real.coe_toNNReal t ht.1.le] at hu
    have he := ((centeredComplexLpCLM Q).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t hu
    change HasDerivAt (fun s : ℝ => centeredComplexLpCLM Q (P s.toNNReal μ))
      (centeredComplexLpCLM Q (P t.toNNReal g)) t at he
    simp only [centeredComplexLpCLM_apply, hcent] at he
    simpa only [neg_zero] using
      c4BackwardGaussian_hasDerivAt Q ⟨0, by omega⟩ 0 q T t (ht.2.trans hbT) he
  have heq (t : ℝ) (ht : t ∈ Ioo 0 b) : Ψ t =
      c3BackwardFluxFunctional hd Q (.inr false) 0 T
        (fun r j => ClockAnalyticity.flux Q (fun k => hP.gradientOrbit μ (r : ℝ) k) j) q t :=
    (hdF t ht).unique (clock_unforced_backward_flux_hasDerivAt hd D Q hQ μ hμ P hP
      q T t ht.1 (ht.2.trans hbT))
  have hi' := hi.congr_uIoo (by
    intro t ht
    exact heq t (by simpa only [uIoo_of_le hb.le] using ht))
  refine ⟨hi', ?_⟩
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hb
    hdF hi hF.continuousAt.continuousWithinAt
    (hF.continuousAt.tendsto.mono_left nhdsWithin_le_nhds)
  have hzero : P 0 μ = μ := by rw [hP.1, ContinuousLinearMap.id_apply]
  calc
    _ = F b - F 0 := by
      dsimp only [F]
      simp only [Real.toNNReal_zero, sub_zero, hzero]
    _ = ∫ t in (0 : ℝ)..b, Ψ t := hFTC.symm
    _ = _ := intervalIntegral.integral_congr_uIoo (by
      intro t ht
      exact heq t (by simpa only [uIoo_of_le hb.le] using ht))

/-- The initial Gaussian defect is the time-zero canonical flux pairing,
with the positive smoothing time incorporated into the backward test. -/
theorem clock_initial_gaussian_defect_pairing
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ)
    (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (b s : ℝ) (hb : 0 < b) (hs : 0 < s) (g : Lp ℂ 2 (reducedLaw Q)) :
    c4EndpointPairing Q (gaussianAverage hd Q s hs
      (centeredComplexLp Q (P b.toNNReal μ) -
        homogeneousGaussianEvolution Q ⟨0, by omega⟩ 0 b.toNNReal
          (centeredComplexLp Q μ))) g =
      ∫ t in (0 : ℝ)..b, c3BackwardFluxFunctional hd Q (.inr false) 0 (b+s)
        (fun r j => ClockAnalyticity.flux Q (fun k => hP.gradientOrbit μ (r : ℝ) k) j) g t := by
  have h := (clock_unforced_initial_pairing_variation hd D Q hQ μ hμ P hP
    g (b+s) b hb (by linarith)).2
  have hsb : (b+s-b).toNNReal = s.toNNReal := by congr 1; ring
  rw [hsb] at h
  have hbs : 0 < b+s := by positivity
  have hb' : 0 < (b.toNNReal : ℝ) := by rwa [Real.coe_toNNReal b hb.le]
  have hs' : 0 < (s.toNNReal : ℝ) := by rwa [Real.coe_toNNReal s hs.le]
  have hbs' : 0 < ((b+s).toNNReal : ℝ) := by rwa [Real.coe_toNNReal _ hbs.le]
  rw [homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ 0 s.toNNReal hs',
    homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ 0 (b+s).toNNReal hbs'] at h
  simp only [Real.coe_toNNReal s hs.le, Real.coe_toNNReal _ hbs.le] at h
  rw [← h]
  change c4EndpointPairing Q (homogeneousAverage Q ⟨0, by omega⟩ s hs 0 _) g = _
  rw [c4EndpointPairing_homogeneousAverage, neg_zero, map_sub, ContinuousLinearMap.sub_apply]
  congr 1
  rw [homogeneousGaussianEvolution_pos Q ⟨0, by omega⟩ 0 b.toNNReal hb']
  simp only [Real.coe_toNNReal b hb.le]
  rw [c4EndpointPairing_homogeneousAverage, neg_zero, homogeneousAverage_add]

/-- The actual coefficient at every physical point is essentially bounded. -/
theorem clock_coefficient_memLp_at {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (x : Vec d) (j k : Fin d) :
    MemLp (fun ω : FieldPair d => (ω.1 x j k : ℂ)) ∞ (reducedLaw Q) := by
  have h := (memLp_reduced_coefficient_complex Q j k).comp_measurePreserving
    (measurePreserving_translate (reducedLaw Q) (reducedLaw_stationary Q) x)
  simpa only [Function.comp_def, translate_matrix, add_zero] using h

/-- Multiplication by the actual coefficient at a physical point. -/
def clockCoefficientMulAt {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (x : Vec d) (j k : Fin d) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL (reducedLaw Q) ∞ 2 2
    ((clock_coefficient_memLp_at Q x j k).toLp (fun ω => (ω.1 x j k : ℂ)))

/-- The physical multiplier retains its literal coefficient representative. -/
theorem clockCoefficientMulAt_coe {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (x : Vec d) (j k : Fin d)
    (f : Lp ℂ 2 (reducedLaw Q)) :
    clockCoefficientMulAt Q x j k f =ᵐ[reducedLaw Q]
      fun ω => (ω.1 x j k : ℂ) * f ω := by
  have hc := (clock_coefficient_memLp_at Q x j k).coeFn_toLp
  have hm := (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder (r := 2)
    ((clock_coefficient_memLp_at Q x j k).toLp (fun ω => (ω.1 x j k : ℂ))) f
  filter_upwards [hc, hm] with ω ha hb
  simpa only [clockCoefficientMulAt, ContinuousLinearMap.holderL_apply_apply,
    ContinuousLinearMap.mul_apply', ha] using hb

/-- Conditional projection onto the literal joint fields in a spatial set. -/
def clockLocalProjection {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) :
    Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q) :=
  (lpMeas ℂ ℂ (localSigma U) 2 (reducedLaw Q)).subtypeL.comp
    (condExpL2 ℂ ℂ (Probability.localSigma_le_borel U))

/-- The Hilbert projection and the usual conditional expectation agree. -/
theorem clockLocalProjection_ae_condExp {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (f : Lp ℂ 2 (reducedLaw Q)) :
    clockLocalProjection Q U f =ᵐ[reducedLaw Q] (reducedLaw Q)[⇑f | localSigma U] := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have h := (Lp.memLp f).condExpL2_ae_eq_condExp (𝕜 := ℂ)
    (Probability.localSigma_le_borel U)
  simpa only [Lp.toLp_coeFn, clockLocalProjection, ContinuousLinearMap.comp_apply,
    Submodule.subtypeL_apply] using h

/-- Within the retained region, conditioning commutes with each actual
anisotropic coefficient entry. Local measurability follows from field evaluation. -/
theorem clockLocalProjection_coefficient_commute {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (x : Vec d) (hx : x ∈ U)
    (j k : Fin d) (f : Lp ℂ 2 (reducedLaw Q)) :
    clockLocalProjection Q U (clockCoefficientMulAt Q x j k f) =
      clockCoefficientMulAt Q x j k (clockLocalProjection Q U f) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have heval : Measurable[localSigma U]
      (fun ω : FieldPair d => (ω.1 x, ω.2 x)) :=
    Measurable.of_comap_le (le_iSup_of_le ⟨x, hx⟩ le_rfl)
  have ha : Measurable[localSigma U] (fun ω : FieldPair d => (ω.1 x j k : ℂ)) :=
    Complex.measurable_ofReal.comp
      (((continuous_id : Continuous (fun M : Mat d => M)).matrix_elem j k).measurable.comp heval.fst)
  have hp : Integrable (fun ω : FieldPair d => (ω.1 x j k : ℂ) * f ω) (reducedLaw Q) := by
    convert ((Lp.memLp f).integrable (by norm_num)).mul_of_top_left
      (clock_coefficient_memLp_at Q x j k) using 1
    ext ω
    exact mul_comm _ _
  have h := condExp_bilin_of_aestronglyMeasurable_left (ContinuousLinearMap.mul ℝ ℂ)
    ha.stronglyMeasurable.aestronglyMeasurable hp ((Lp.memLp f).integrable (by norm_num))
  have hc := condExp_congr_ae (m := localSigma U) (clockCoefficientMulAt_coe Q x j k f)
  apply Lp.ext
  filter_upwards [clockLocalProjection_ae_condExp Q U (clockCoefficientMulAt Q x j k f),
    hc, h, clockLocalProjection_ae_condExp Q U f,
    clockCoefficientMulAt_coe Q x j k (clockLocalProjection Q U f)] with ω h₁ h₂ h₃ h₄ h₅
  simpa only [ContinuousLinearMap.mul_apply', h₁, h₂, h₄, h₅] using h₃

/-- The joint-field projection is an L² contraction. -/
theorem clockLocalProjection_norm_le {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (f : Lp ℂ 2 (reducedLaw Q)) :
    ‖clockLocalProjection Q U f‖ ≤ ‖f‖ :=
  norm_condExpL2_coe_le (Probability.localSigma_le_borel U) f

/-- A genuinely joint-local representative is fixed by this projection. -/
theorem clockLocalProjection_eq_self {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (f : Lp ℂ 2 (reducedLaw Q))
    (hf : AEStronglyMeasurable[localSigma U] (⇑f) (reducedLaw Q)) :
    clockLocalProjection Q U f = f := by
  let : Fact (localSigma U ≤ borel (FieldPair d)) :=
    ⟨Probability.localSigma_le_borel U⟩
  have hmem : f ∈ lpMeas ℂ ℂ (localSigma U) 2 (reducedLaw Q) :=
    mem_lpMeas_iff_aestronglyMeasurable.mpr hf
  let v : lpMeas ℂ ℂ (localSigma U) 2 (reducedLaw Q) := ⟨f, hmem⟩
  change (((lpMeas ℂ ℂ (localSigma U) 2 (reducedLaw Q)).orthogonalProjectionOnto v) :
    Lp ℂ 2 (reducedLaw Q)) = f
  exact congrArg Subtype.val (Submodule.orthogonalProjectionOnto_mem_subspace_eq_self v)

/-- The literal initial clock has no projection error at a retained point. -/
theorem clockLocalProjection_initial_clock {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (x : Vec d) (hx : x ∈ U)
    (μ : Lp ℂ 2 (reducedLaw Q)) (hμ : IsReducedClockObservation Q μ) :
    clockLocalProjection Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x μ) =
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x μ := by
  have heval : Measurable[localSigma U]
      (fun ω : FieldPair d => (ω.1 x, ω.2 x)) :=
    Measurable.of_comap_le (le_iSup_of_le ⟨x, hx⟩ le_rfl)
  have hm : Measurable[localSigma U] (fun ω : FieldPair d => (ω.2 x : ℂ)) :=
    Complex.measurable_ofReal.comp heval.snd
  have htrans := (measurePreserving_translate (reducedLaw Q)
    (reducedLaw_stationary Q) x).quasiMeasurePreserving.ae hμ
  have hrep : (fun ω : FieldPair d => (ω.2 x : ℂ)) =ᵐ[reducedLaw Q]
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x μ := by
    filter_upwards [htrans, coeFn_complexTranslation (reducedLaw Q)
      (reducedLaw_stationary Q) x μ] with ω h₁ h₂
    simpa only [translate_scalar, add_zero] using h₁.symm.trans h₂.symm
  exact clockLocalProjection_eq_self Q U _
    (hm.stronglyMeasurable.aestronglyMeasurable.congr hrep)

/-- The physical orbit of a strong horizontal derivative differentiates in
its actual coordinate direction at every spatial point. -/
theorem clock_translation_line_deriv {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (j : Fin d) (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g)
    (x : Vec d) :
    HasLineDerivAt ℝ
      (fun y => complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) y f)
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) x (unitVector j) := by
  have hzero := hfg.hasDerivAt_orbit 0
  simp only [zero_smul, complexTranslation_zero] at hzero
  have hrec := ((complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x).toContinuousLinearMap.restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt_of_eq 0 hzero rfl
  simpa only [HasLineDerivAt, Function.comp_def, ContinuousLinearMap.coe_restrictScalars',
    LinearIsometry.coe_toContinuousLinearMap, ← complexTranslation_add] using hrec

/-- Conditioning preserves the physical weak gradient of the actual orbit.
The sigma algebra is fixed in space, while the physical orbit is translated. -/
theorem clockLocalProjection_spatial_weak_gradient {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (U : Set (Vec d)) (j : Fin d)
    (f g : Lp ℂ 2 (reducedLaw Q))
    (hfg : HasComplexHorizontalDerivative (reducedLaw Q) (reducedLaw_stationary Q) j f g)
    (φ : Vec d → ℝ) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hφc : HasCompactSupport φ) :
    (∫ x : Vec d, coordinateDerivative j φ x • clockLocalProjection Q U
      (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)) =
      - ∫ x : Vec d, φ x • clockLocalProjection Q U
        (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let B := (clockLocalProjection Q U).restrictScalars ℝ
  let u : Vec d → Lp ℂ 2 (reducedLaw Q) := fun x => B
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)
  let v : Vec d → Lp ℂ 2 (reducedLaw Q) := fun x => B
    (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x g)
  have hu : Continuous u := B.continuous.comp
    ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  have hv : Continuous v := B.continuous.comp
    ((continuous_complexTranslation _ _).comp (continuous_id.prodMk continuous_const))
  have hφ' : Continuous (coordinateDerivative j φ) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hφ'c : HasCompactSupport (coordinateDerivative j φ) :=
    hφc.fderiv_apply ℝ (unitVector j)
  have hφline (x : Vec d) :
      HasLineDerivAt ℝ φ (coordinateDerivative j φ x) x (unitVector j) :=
    (hφ.differentiable (by simp) x).hasFDerivAt.hasLineDerivAt _
  have huline (x : Vec d) : HasLineDerivAt ℝ u (v x) x (unitVector j) := by
    exact B.hasFDerivAt.comp_hasDerivAt_of_eq 0
      (clock_translation_line_deriv Q j f g hfg x) rfl
  have hiu : Integrable (fun x => φ x • u x) :=
    (hφ.continuous.smul hu).integrable_of_hasCompactSupport hφc.smul_right
  have hiv : Integrable (fun x => φ x • v x) :=
    (hφ.continuous.smul hv).integrable_of_hasCompactSupport hφc.smul_right
  have hiu' : Integrable (fun x => coordinateDerivative j φ x • u x) :=
    (hφ'.smul hu).integrable_of_hasCompactSupport hφ'c.smul_right
  have hparts := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (E := Vec d) (F := ℝ) (G := Lp ℂ 2 (reducedLaw Q))
    (W := Lp ℂ 2 (reducedLaw Q)) (μ := volume) (B := ContinuousLinearMap.lsmul ℝ ℝ)
    hiu' hiv hiu (fun x _ => hφline x) (fun x _ => huline x)
  simpa only [neg_neg, ContinuousLinearMap.lsmul_apply, u, v, B,
    ContinuousLinearMap.coe_restrictScalars'] using
    (congrArg Neg.neg hparts).symm

/-- A compact spatial test has the literal physical translation integral as
its L²-valued Bochner representative. -/
theorem clock_translation_test_integral_coe {d : ℕ} {Λ r : ℝ}
    (Q : EnvironmentLaw d Λ r) (f : Lp ℂ 2 (reducedLaw Q))
    (φ : Vec d → ℝ) (hφ : Continuous φ) (hφc : HasCompactSupport φ) :
    (∫ x : Vec d, φ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) =ᵐ[reducedLaw Q]
      fun ω => ∫ x : Vec d, (φ x : ℂ) * f (translate x ω) := by
  let : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  have hu : Integrable (fun x : Vec d => φ x •
      complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) :=
    (hφ.smul ((continuous_complexTranslation _ _).comp
      (continuous_id.prodMk continuous_const))).integrable_of_hasCompactSupport
        hφc.smul_right
  have hmeas : Measurable (fun p : Vec d × FieldPair d =>
      (φ p.1 : ℂ) * f (translate p.1 p.2)) :=
    (Complex.measurable_ofReal.comp (hφ.measurable.comp measurable_fst)).mul
      ((Lp.stronglyMeasurable f).measurable.comp Probability.continuous_translate.measurable)
  apply coeFn_integral_joint_l2_representative hu hmeas
  intro x
  filter_upwards [coeFn_complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f,
    Lp.coeFn_smul (φ x) (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f)]
    with ω h₁ h₂
  change (φ x • complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) ω =
    φ x • (complexTranslation (reducedLaw Q) (reducedLaw_stationary Q) x f) ω at h₂
  rw [h₂, h₁]
  simp only [Complex.real_smul, smul_eq_mul]

/- Exact supervisor contract; replace with ONE complete proof, no scaffold commit.
theorem clock_unforced_full_gaussian_smoothing
    : ∀ (havg : node_e_u3A_clock_u2D_averageStmt) (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
      ∃ C t₀ : ℝ, 0 < C ∧ 1 ≤ t₀ ∧
      ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
        (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)) (μ : Lp ℂ 2 (reducedLaw Q)),
        IsReducedCoefficientObservation Q a → IsReducedClockObservation Q μ →
      ∀ (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
        IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P →
      ∀ τ : ℝ≥0, t₀ ≤ (τ : ℝ) →
      ∀ (s : ℝ) (hs : 0 < s), 2*(τ : ℝ) ≤ s →
        ‖gaussianAverage hd Q s hs (centeredComplexLp Q (P τ μ) -
          centeredComplexLp Q μ)‖ ≤
          C * s ^ (-(d : ℝ)/4) * ((τ : ℝ)/s + Real.sqrt ((τ : ℝ)/s)) := by
-/
end EinsteinFull.Blueprint

