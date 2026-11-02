import EinsteinFull.Calculus.ComplexForcedGradientSupport

/-!
# Duhamel's formula on every complex L2 datum

The actual positive-time horizontal gradient is extended by zero at nonpositive
real times solely to specify its Bochner integral. Its integrable inverse-square-
root bound permits passage from the full generator domain to arbitrary data.
-/

open MeasureTheory Filter Set
open scoped NNReal Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

/-- The actual gradient orbit at positive times, with zero values outside that interval. -/
def IsComplexEnvironmentSemigroup.gradientOrbit
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    (s : ℝ) : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
  if hs : 0 < s then hP.forcedGradient s.toNNReal (by simpa using hs) f else 0

/-- At positive time the extended orbit is the actual horizontal gradient. -/
theorem IsComplexEnvironmentSemigroup.gradientOrbit_spec
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {s : ℝ} (hs : 0 < s) :
    HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P s.toNNReal f) (hP.gradientOrbit f s) := by
  simp only [IsComplexEnvironmentSemigroup.gradientOrbit, dif_pos hs]
  exact hP.forcedGradient_spec _ _ f

/-- The extended gradient orbit is strongly continuous throughout positive real time. -/
theorem IsComplexEnvironmentSemigroup.continuousOn_gradientOrbit
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q)) :
    ContinuousOn (hP.gradientOrbit f) (Ioi 0) := by
  rw [continuousOn_iff_continuous_restrict]
  have hc : Continuous (fun s : Ioi (0 : ℝ) =>
      (⟨s.1.toNNReal, Real.toNNReal_pos.mpr s.2⟩ : {t : ℝ≥0 // 0 < t})) :=
    (continuous_real_toNNReal.comp continuous_subtype_val).subtype_mk _
  apply Continuous.congr ((hP.continuous_forcedGradient_apply f).comp hc)
  intro s
  change _ = hP.gradientOrbit f s.1
  simp only [IsComplexEnvironmentSemigroup.gradientOrbit,
    dif_pos (show 0 < s.1 from s.2), Function.comp_apply]

/-- A common finite-horizon inverse-square-root majorant for every actual gradient orbit. -/
theorem IsComplexEnvironmentSemigroup.norm_gradientOrbit_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P) (f : Lp ℂ 2 (reducedLaw Q))
    {t s : ℝ} (hs : 0 < s) (hst : s ≤ t) :
    ‖hP.gradientOrbit f s‖ ≤
      (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
        Real.exp (65 * complexForceShift d Λ₀ ζ * t) * ‖f‖) * (Real.sqrt s)⁻¹ := by
  have hb := (hP.forcedGradient s.toNNReal (by simpa using hs)).le_opNorm f
  have he : Real.exp (65 * complexForceShift d Λ₀ ζ * s) ≤
      Real.exp (65 * complexForceShift d Λ₀ ζ * t) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hst (by
      have := complexForceShift_nonneg Q ζ
      positivity))
  simp only [IsComplexEnvironmentSemigroup.gradientOrbit, dif_pos hs]
  apply hb.trans
  have hn := mul_le_mul_of_nonneg_right
    (hP.norm_forcedGradient_le s.toNNReal (by simpa using hs)) (norm_nonneg f)
  rw [Real.coe_toNNReal s hs.le] at hn
  exact hn.trans (by
    rw [div_eq_mul_inv]
    nlinarith [mul_le_mul_of_nonneg_left he
      (show 0 ≤ 2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * (Real.sqrt s)⁻¹ * ‖f‖ by positivity)])

private theorem continuousOn_drift
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    ContinuousOn (fun s : ℝ => R (Real.toNNReal (t-s))
      (complexForceDrift Q i (hP.gradientOrbit f s))) (Ioi 0) := by
  have hRj := hR.continuous_unforced_apply
    (α := (ℝ≥0 × Lp ℂ 2 (reducedLaw Q))) continuous_fst continuous_snd
  exact hRj.comp_continuousOn
    ((continuous_real_toNNReal.comp (continuous_const.sub continuous_id)).continuousOn.prodMk
      ((complexForceDrift Q i).continuous.comp_continuousOn (hP.continuousOn_gradientOrbit f)))

private theorem norm_drift_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) {s : ℝ} (hs : s ∈ Ioc (0 : ℝ) t) :
    ‖R (Real.toNNReal (t-s)) (complexForceDrift Q i (hP.gradientOrbit f s))‖ ≤
      (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
          Real.exp (65 * complexForceShift d Λ₀ ζ * t) * ‖f‖)) * (Real.sqrt s)⁻¹ := by
  exact (hR.norm_unforced_apply_le _ _).trans
    ((norm_complexForceDrift_apply_le Q i _).trans (by
      have hΛ : 0 ≤ Λ₀ := zero_le_one.trans Q.ellipticity_parameter
      calc
        _ ≤ ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
            ((2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
              Real.exp (65 * complexForceShift d Λ₀ ζ * t) * ‖f‖) * (Real.sqrt s)⁻¹) :=
          mul_le_mul_of_nonneg_left (hP.norm_gradientOrbit_le f hs.1 hs.2) (by positivity)
        _ = _ := by ring))

/-- The Duhamel drift for arbitrary complex L2 data is Bochner integrable. -/
theorem IsComplexEnvironmentSemigroup.intervalIntegrable_mild_drift
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    IntervalIntegrable (fun s : ℝ => R (Real.toNNReal (t-s))
      (complexForceDrift Q i (hP.gradientOrbit f s))) volume 0 t := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)]
  apply ((intervalIntegrable_inv_sqrt t.property).const_mul
    (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
      (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
        Real.exp (65 * complexForceShift d Λ₀ ζ * t) * ‖f‖))).1.mono'
  · exact ((continuousOn_drift hP hR f t).mono (fun _ hs => hs.1)).aestronglyMeasurable
      measurableSet_Ioc
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact norm_drift_le hP hR f t hs

private theorem integral_gradientOrbit_of_generator
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R)
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) (t : ℝ≥0) :
    ζ • (∫ s in (0 : ℝ)..(t : ℝ), R (Real.toNNReal (t-s))
      (complexForceDrift Q i (hP.gradientOrbit f s))) = P t f - R t f := by
  obtain ⟨G, _, hG⟩ := hP.exists_continuous_gradient_orbit hfg
  have he : (∫ s in (0 : ℝ)..(t : ℝ), R (Real.toNNReal (t-s))
      (complexForceDrift Q i (hP.gradientOrbit f s))) =
      ∫ s in (0 : ℝ)..(t : ℝ), R (Real.toNNReal (t-s)) (complexForceDrift Q i (G s)) := by
    apply intervalIntegral.integral_congr_ae
    apply Eventually.of_forall
    intro s hs
    rw [uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hs
    have he : hP.gradientOrbit f s = G s :=
      WithLp.ofLp_injective 2 ((hP.gradientOrbit_spec f hs.1).unique (hG s))
    rw [he]
  rw [he]
  exact hP.integral_force_drift hR hfg hG t

/-- Variation of constants for every complex L2 datum, with its actual positive-time gradient. -/
theorem IsComplexEnvironmentSemigroup.integral_mild_force_drift
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    ζ • (∫ s in (0 : ℝ)..(t : ℝ), R (Real.toNNReal (t-s))
      (complexForceDrift Q i (hP.gradientOrbit f s))) = P t f - R t f := by
  let u := fun n => forcedComplexResolventApproximation Q i ζ n f
  have hu : Tendsto u atTop (𝓝 f) := tendsto_forcedComplexResolventApproximation Q i ζ f
  have hun (n : ℕ) : ‖u n‖ ≤ ‖f‖ := norm_forcedComplexResolventApproximation_le Q i ζ n f
  let F := fun (n : ℕ) (s : ℝ) => R (Real.toNNReal (t-s))
    (complexForceDrift Q i (hP.gradientOrbit (u n) s))
  let C := ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
    (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      Real.exp (65 * complexForceShift d Λ₀ ζ * t) * ‖f‖)
  have hlim : Tendsto (fun n => ∫ s in (0 : ℝ)..(t : ℝ), F n s) atTop
      (𝓝 (∫ s in (0 : ℝ)..(t : ℝ), R (Real.toNNReal (t-s))
        (complexForceDrift Q i (hP.gradientOrbit f s)))) := by
    apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (fun s => C * (Real.sqrt s)⁻¹)
    · apply Eventually.of_forall
      intro n
      rw [uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)]
      exact (hP.intervalIntegrable_mild_drift hR (u n) t).aestronglyMeasurable
    · apply Eventually.of_forall
      intro n
      apply Eventually.of_forall
      intro s hs
      rw [uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hs
      apply (norm_drift_le hP hR (u n) t hs).trans
      dsimp [C]
      have hΛ : 0 ≤ Λ₀ := zero_le_one.trans Q.ellipticity_parameter
      gcongr
      exact hun n
    · exact (intervalIntegrable_inv_sqrt t.property).const_mul C
    · apply Eventually.of_forall
      intro s hs
      rw [uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] at hs
      have hG : Tendsto (fun n => hP.gradientOrbit (u n) s) atTop
          (𝓝 (hP.gradientOrbit f s)) := by
        simp only [IsComplexEnvironmentSemigroup.gradientOrbit, dif_pos hs.1]
        exact ((hP.forcedGradient s.toNNReal (by simpa using hs.1)).continuous.tendsto f).comp hu
      exact ((R (Real.toNNReal (t-s))).continuous.tendsto _).comp
        (((complexForceDrift Q i).continuous.tendsto _).comp hG)
  have he (n : ℕ) : ζ • (∫ s in (0 : ℝ)..(t : ℝ), F n s) = P t (u n) - R t (u n) :=
    integral_gradientOrbit_of_generator hP hR (forcedComplexYosida_graph Q i ζ n f) t
  have hl := (((P t).continuous.tendsto f).comp hu).sub
    (((R t).continuous.tendsto f).comp hu)
  change Tendsto (fun n => P t (u n) - R t (u n)) atTop (𝓝 (P t f - R t f)) at hl
  simp_rw [← he] at hl
  exact tendsto_nhds_unique (hlim.const_smul ζ) hl

/-- Every complex L2 datum satisfies the actual forward Duhamel identity. -/
theorem IsComplexEnvironmentSemigroup.mild_duhamel
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    P t f = R t f + ζ • (∫ s in (0 : ℝ)..(t : ℝ), R (Real.toNNReal (t-s))
      (complexForceDrift Q i (hP.gradientOrbit f s))) := by
  rw [hP.integral_mild_force_drift hR f t, add_sub_cancel]

/-- The forced/unforced difference has an explicit square-root-time bound on every datum. -/
theorem IsComplexEnvironmentSemigroup.norm_sub_unforced_mild_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    ‖P t f - R t f‖ ≤
      (4 * ‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * Real.sqrt (t : ℝ) *
          Real.exp (65 * complexForceShift d Λ₀ ζ * t)) * ‖f‖ := by
  let C := ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
    (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      Real.exp (65 * complexForceShift d Λ₀ ζ * t) * ‖f‖)
  have hb := intervalIntegral.norm_integral_le_of_norm_le
    (a := (0 : ℝ)) (b := (t : ℝ)) (μ := volume) t.property
    (Eventually.of_forall fun s hs => norm_drift_le hP hR f t hs)
    ((intervalIntegrable_inv_sqrt t.property).const_mul C)
  rw [← hP.integral_mild_force_drift hR f t, norm_smul]
  calc
    _ ≤ ‖ζ‖ * (∫ s in (0 : ℝ)..(t : ℝ), C * (Real.sqrt s)⁻¹) :=
      mul_le_mul_of_nonneg_left hb (norm_nonneg ζ)
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      rw [integral_inv_sqrt (t := (t : ℝ)) t.property]
      dsimp [C]
      ring

/-- The same estimate holds in operator norm for the actual forced/unforced semigroups. -/
theorem IsComplexEnvironmentSemigroup.opNorm_sub_unforced_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (t : ℝ≥0) :
    ‖P t - R t‖ ≤
      4 * ‖ζ‖ * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * Real.sqrt (t : ℝ) *
          Real.exp (65 * complexForceShift d Λ₀ ζ * t) := by
  have hΛ : 0 ≤ Λ₀ := zero_le_one.trans Q.ellipticity_parameter
  exact (P t - R t).opNorm_le_bound (by positivity)
    (fun f => hP.norm_sub_unforced_mild_le hR f t)

end EinsteinFull
