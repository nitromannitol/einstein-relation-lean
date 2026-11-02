import EinsteinFull.Calculus.ComplexMildDuhamelSupport
import EinsteinFull.Calculus.ComplexForceEvolutionGeneratorSupport
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Full-horizon forward gradient energy for arbitrary stationary L² data

Only production imports are used. Actual normalized resolvents provide continuous
full-generator-domain gradient orbits; their energy estimate passes to all L²
initial data by Fatou. The existing `gradientOrbit` specifies zero at nonpositive
times and equals `forcedGradient` at every positive time. No gradient of the
initial datum is asserted at zero. In particular, the square of the pointwise
inverse-square-root smoothing bound is never integrated near zero.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ}

private lemma integral_nonneg_limit_le {μ : Measure ℝ} {F : ℕ → ℝ → ℝ}
    {f : ℝ → ℝ} {C : ℝ}
    (hF : ∀ n, Integrable (F n) μ) (hn : ∀ n s, 0 ≤ F n s)
    (hf : ∀ s, 0 ≤ f s)
    (hl : ∀ᵐ s ∂μ, Tendsto (fun n => F n s) atTop (𝓝 (f s)))
    (hb : ∀ n, ∫ s, F n s ∂μ ≤ C) :
    Integrable f μ ∧ (∫ s, f s ∂μ) ≤ C := by
  have he (n : ℕ) : (∫⁻ s, ‖F n s‖ₑ ∂μ) ≤ ENNReal.ofReal C := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hF n)]
    simpa only [Real.norm_eq_abs, abs_of_nonneg (hn n _)] using ENNReal.ofReal_le_ofReal (hb n)
  have hlim : liminf (fun n => ∫⁻ s, ‖F n s‖ₑ ∂μ) atTop ≤ ENNReal.ofReal C :=
    liminf_le_of_frequently_le' (Frequently.of_forall he)
  have hi : Integrable f μ := integrable_of_tendsto hl
    (fun n => (hF n).aestronglyMeasurable) (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hlim)
  refine ⟨hi, ?_⟩
  have hh := (lintegral_enorm_le_liminf_of_tendsto hl
    (fun n => (hF n).aestronglyMeasurable.aemeasurable.enorm)).trans hlim
  rw [← ofReal_integral_norm_eq_lintegral_enorm hi] at hh
  simp only [Real.norm_eq_abs, abs_of_nonneg (hf _)] at hh
  exact (ENNReal.ofReal_le_ofReal_iff ((integral_nonneg (hn 0)).trans (hb 0))).mp hh

/-- At every time the actual gradient is linear in the initial datum, including
its stipulated zero extension at nonpositive times. -/
theorem IsComplexEnvironmentSemigroup.gradientOrbit_sub_fullHorizon
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f g : Lp ℂ 2 (reducedLaw Q)) (s : ℝ) :
    hP.gradientOrbit (f-g) s = hP.gradientOrbit f s - hP.gradientOrbit g s := by
  by_cases hs : 0 < s
  · simp only [IsComplexEnvironmentSemigroup.gradientOrbit, dif_pos hs, map_sub]
  · simp only [IsComplexEnvironmentSemigroup.gradientOrbit, dif_neg hs, sub_self]

/-- Resolvent convergence is preserved by the actual positive-time horizontal
gradient operator; no common graph-density premise is used. -/
theorem IsComplexEnvironmentSemigroup.tendsto_gradientOrbit_resolvent_fullHorizon
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (s : ℝ) :
    Tendsto (fun n => hP.gradientOrbit (forcedComplexResolventApproximation Q i ζ n f) s)
      atTop (𝓝 (hP.gradientOrbit f s)) := by
  by_cases hs : 0 < s
  · simp only [IsComplexEnvironmentSemigroup.gradientOrbit, dif_pos hs]
    exact ((hP.forcedGradient s.toNNReal (by simpa using hs)).continuous.tendsto f).comp
      (tendsto_forcedComplexResolventApproximation Q i ζ f)
  · simp only [IsComplexEnvironmentSemigroup.gradientOrbit, dif_neg hs]
    exact tendsto_const_nhds

/-- Actual all-L² gradient energy is integrable down to time zero and satisfies
the full-domain structural estimate. Fatou is applied to actual resolvent orbits. -/
theorem IsComplexEnvironmentSemigroup.integrable_sq_gradientOrbit_fullHorizon
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (T : ℝ≥0) :
    IntegrableOn (fun s => ‖hP.gradientOrbit f s‖ ^ 2) (Ioc (0 : ℝ) T) ∧
      (∫ s in (0 : ℝ)..(T : ℝ), ‖hP.gradientOrbit f s‖ ^ 2) ≤
        2 * (Real.exp (2 * Λ₀) * Λ₀) *
          Real.exp (2 * complexForceShift d Λ₀ ζ * T) * ‖f‖ ^ 2 := by
  let u := fun n => forcedComplexResolventApproximation Q i ζ n f
  have he (n : ℕ) := hP.exists_continuous_gradient_orbit (forcedComplexYosida_graph Q i ζ n f)
  choose G hGc hG using he
  have hid (n : ℕ) (s : ℝ) (hs : 0 < s) : hP.gradientOrbit (u n) s = G n s :=
    WithLp.ofLp_injective 2 ((hP.gradientOrbit_spec (u n) hs).unique (hG n s))
  have hbound (n : ℕ) : (∫ s in Ioc (0 : ℝ) T, ‖G n s‖ ^ 2) ≤
      2 * (Real.exp (2 * Λ₀) * Λ₀) * Real.exp (2 * complexForceShift d Λ₀ ζ * T) * ‖f‖ ^ 2 := by
    rw [← intervalIntegral.integral_of_le (μ := volume) (a := (0 : ℝ)) (b := (T : ℝ)) T.property]
    apply (hP.integral_gradient_le (forcedComplexYosida_graph Q i ζ n f) (hG n) T).trans
    apply mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (norm_forcedComplexResolventApproximation_le Q i ζ n f) 2)
    have hΛ : 0 ≤ Λ₀ := zero_le_one.trans Q.ellipticity_parameter
    positivity
  have hl : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) T),
      Tendsto (fun n => ‖G n s‖ ^ 2) atTop (𝓝 (‖hP.gradientOrbit f s‖ ^ 2)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    simpa only [← hid _ _ hs.1] using (hP.tendsto_gradientOrbit_resolvent_fullHorizon f s).norm.pow 2
  obtain ⟨hi, hb⟩ := integral_nonneg_limit_le
    (fun n => ((hGc n).norm.pow 2).continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (fun n s => sq_nonneg ‖G n s‖) (fun s => sq_nonneg ‖hP.gradientOrbit f s‖) hl hbound
  exact ⟨hi, by simpa only [intervalIntegral.integral_of_le (μ := volume) (a := (0 : ℝ)) (b := (T : ℝ)) T.property] using hb⟩

/-- The normalized heterogeneous resolvents converge in the genuine integrated
Euclidean gradient energy on the entire horizon. -/
theorem IsComplexEnvironmentSemigroup.tendsto_integral_sq_gradientOrbit_resolvent_fullHorizon
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (T : ℝ≥0) :
    Tendsto (fun n => ∫ s in (0 : ℝ)..(T : ℝ),
      ‖hP.gradientOrbit (forcedComplexResolventApproximation Q i ζ n f) s -
        hP.gradientOrbit f s‖ ^ 2) atTop (𝓝 0) := by
  simp_rw [← hP.gradientOrbit_sub_fullHorizon]
  have hl := ((tendsto_forcedComplexResolventApproximation Q i ζ f).sub_const f).norm.pow 2
  simp only [sub_self, norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)] at hl
  apply squeeze_zero
    (fun n => intervalIntegral.integral_nonneg T.property (fun s _ => sq_nonneg _))
    (fun n => (hP.integrable_sq_gradientOrbit_fullHorizon
      (forcedComplexResolventApproximation Q i ζ n f - f) T).2)
  simpa only [mul_zero] using hl.const_mul
    (2 * (Real.exp (2 * Λ₀) * Λ₀) * Real.exp (2 * complexForceShift d Λ₀ ζ * T))


/-- The specified endpoint value is zero, also for initial data without a gradient. -/
theorem IsComplexEnvironmentSemigroup.gradientOrbit_zero_fullHorizon
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    hP.gradientOrbit f 0 = 0 := by
  simp only [IsComplexEnvironmentSemigroup.gradientOrbit, dif_neg (lt_irrefl (0 : ℝ))]

/-- The squared actual gradient is integrable on the closed horizon, including
its explicit zero endpoint, for every nonnegative real horizon. -/
theorem IsComplexEnvironmentSemigroup.integrableOn_Icc_sq_gradientOrbit_fullHorizon
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) {T : ℝ} (hT : 0 ≤ T) :
    IntegrableOn (fun s => ‖hP.gradientOrbit f s‖ ^ 2) (Icc 0 T) ∧
      (∫ s in Icc 0 T, ‖hP.gradientOrbit f s‖ ^ 2) ≤
        2 * (Real.exp (2 * Λ₀) * Λ₀) *
          Real.exp (2 * complexForceShift d Λ₀ ζ * T) * ‖f‖ ^ 2 := by
  have he := hP.integrable_sq_gradientOrbit_fullHorizon f ⟨T, hT⟩
  constructor
  · rw [integrableOn_Icc_iff_integrableOn_Ioc]
    exact he.1
  · rw [integral_Icc_eq_integral_Ioc]
    have hb := he.2
    change (∫ s in (0 : ℝ)..T, ‖hP.gradientOrbit f s‖ ^ 2) ≤ _ at hb
    rwa [intervalIntegral.integral_of_le hT] at hb

/-- The actual gradient defines a genuine Euclidean-valued time-L² class. -/
theorem IsComplexEnvironmentSemigroup.memLp_gradientOrbit_fullHorizon
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (T : ℝ≥0) :
    MemLp (hP.gradientOrbit f) 2 (volume.restrict (Ioc (0 : ℝ) T)) := by
  apply (memLp_two_iff_integrable_sq_norm
    (((hP.continuousOn_gradientOrbit f).mono (fun _ hs => hs.1)).aestronglyMeasurable
      measurableSet_Ioc)).mpr
  exact (hP.integrable_sq_gradientOrbit_fullHorizon f T).1

private lemma norm_toLp_sub_sq_fullHorizon {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {μ : Measure ℝ} {F G : ℝ → E} (hF : MemLp F 2 μ) (hG : MemLp G 2 μ) :
    ‖hF.toLp F-hG.toLp G‖ ^ 2 = ∫ s, ‖F s-G s‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_sub (hF.toLp F) (hG.toLp G), hF.coeFn_toLp, hG.coeFn_toLp]
    with s hsub hf hg
  rw [hsub]
  simp only [Pi.sub_apply, hf, hg, real_inner_self_eq_norm_sq]

/-- The normalized resolvent gradients converge in the actual time-L² norm,
with the limit the same positive-time forced gradient of the original datum. -/
theorem IsComplexEnvironmentSemigroup.tendsto_Lp_gradientOrbit_resolvent_fullHorizon
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (f : Lp ℂ 2 (reducedLaw Q)) (T : ℝ≥0) :
    Tendsto (fun n => (hP.memLp_gradientOrbit_fullHorizon
      (forcedComplexResolventApproximation Q i ζ n f) T).toLp
        (hP.gradientOrbit (forcedComplexResolventApproximation Q i ζ n f))) atTop
      (𝓝 ((hP.memLp_gradientOrbit_fullHorizon f T).toLp (hP.gradientOrbit f))) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have he := hP.tendsto_integral_sq_gradientOrbit_resolvent_fullHorizon f T
  have hl := (Real.continuous_sqrt.tendsto 0).comp he
  simp only [Real.sqrt_zero] at hl
  convert hl using 1
  ext n
  dsimp only [Function.comp_apply]
  rw [intervalIntegral.integral_of_le (μ := volume) (a := (0 : ℝ)) (b := (T : ℝ)) T.property,
    ← norm_toLp_sub_sq_fullHorizon
      (hP.memLp_gradientOrbit_fullHorizon (forcedComplexResolventApproximation Q i ζ n f) T)
      (hP.memLp_gradientOrbit_fullHorizon f T), Real.sqrt_sq (norm_nonneg _)]

/-- A single explicit constant chosen from dimension and ellipticity before
any law, force, semigroup, datum or horizon. -/
def forwardGradientEnergyConstant (d : ℕ) (Λ₀ : ℝ) : ℝ :=
  1 + 2 * |Real.exp (2 * Λ₀) * Λ₀| +
    2 * |Real.exp (2 * Λ₀) * Λ₀| * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2

/-- The structural energy constant is strictly positive for all parameters. -/
theorem forwardGradientEnergyConstant_pos (d : ℕ) (Λ₀ : ℝ) :
    0 < forwardGradientEnergyConstant d Λ₀ := by
  unfold forwardGradientEnergyConstant
  positivity

/-- Uniform full-horizon energy: the explicit constant precedes the actual
joint law and all analytic data, and the signed complex force enters quadratically. -/
theorem forward_fullHorizon_gradient_energy (d : ℕ) (Λ₀ : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ {r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
      (i : Fin d) (ζ : ℂ)
      (P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)),
      ∀ (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
      (T : ℝ), 0 ≤ T →
      IntegrableOn (fun s => ‖hP.gradientOrbit f s‖ ^ 2)
        (Icc 0 T) ∧
      (∫ s in Icc 0 T, ‖hP.gradientOrbit f s‖ ^ 2) ≤
        C * Real.exp (C * ‖ζ‖ ^ 2 * T) * ‖f‖ ^ 2 := by
  refine ⟨forwardGradientEnergyConstant d Λ₀, forwardGradientEnergyConstant_pos d Λ₀, ?_⟩
  intro r₀ Q i ζ P hP f T hT
  obtain ⟨hi, hb⟩ := hP.integrableOn_Icc_sq_gradientOrbit_fullHorizon f hT
  refine ⟨hi, hb.trans ?_⟩
  let K := Real.exp (2 * Λ₀) * Λ₀
  have hK : 0 ≤ K := mul_nonneg (Real.exp_pos _).le
    (zero_le_one.trans Q.ellipticity_parameter)
  have hC₁ : 2 * K ≤ forwardGradientEnergyConstant d Λ₀ := by
    change 2 * K ≤ 1 + 2 * |K| + 2 * |K| * ((d : ℝ) * K) ^ 2
    rw [abs_of_nonneg hK]
    linarith [mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK)
      (sq_nonneg ((d : ℝ) * K))]
  have hC₂ : 2 * K * ((d : ℝ) * K) ^ 2 ≤ forwardGradientEnergyConstant d Λ₀ := by
    change 2 * K * ((d : ℝ) * K) ^ 2 ≤
      1 + 2 * |K| + 2 * |K| * ((d : ℝ) * K) ^ 2
    rw [abs_of_nonneg hK]
    linarith
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg ‖f‖)
  apply mul_le_mul hC₁ _ (Real.exp_pos _).le
    (forwardGradientEnergyConstant_pos d Λ₀).le
  apply Real.exp_le_exp.mpr
  calc
    2 * complexForceShift d Λ₀ ζ * T =
        (2 * K * ((d : ℝ) * K) ^ 2) * ‖ζ‖ ^ 2 * T := by
      unfold complexForceShift K
      ring
    _ ≤ forwardGradientEnergyConstant d Λ₀ * ‖ζ‖ ^ 2 * T :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC₂ (sq_nonneg ‖ζ‖)) hT

end EinsteinFull
