import EinsteinFull.Calculus.ComplexMildDuhamelSupport
import EinsteinFull.Calculus.SqrtBetaSupport

/-!
# The actual gradient Volterra identity on every complex L2 datum

A bounded positive unforced time regularization differentiates mild Duhamel.
The double square-root bound dominates both time endpoints. Strong convergence
and closedness of the actual gradient graph identify the unregularized limit.
-/

open MeasureTheory Filter Set
open scoped Topology NNReal

noncomputable section
namespace EinsteinFull
open EinsteinRelation

variable {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
  {P R : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}

/-- The actual gradient of the unforced propagation of the forced coefficient drift. -/
def IsComplexEnvironmentSemigroup.gradientDuhamelIntegrand
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q))
    (t s : ℝ) : PiLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q)) :=
  hR.gradientOrbit (complexForceDrift Q i (hP.gradientOrbit f s)) (t-s)

/-- A bounded positive unforced gradient differentiates mild Duhamel for every L2 datum. -/
theorem IsComplexEnvironmentSemigroup.regularized_mild_gradient_duhamel
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q))
    (δ : ℝ≥0) (hδ : 0 < δ) (t : ℝ≥0) :
    hR.unforcedGradient δ hδ (P t f) = hR.unforcedGradient δ hδ (R t f) +
      ζ • (∫ s in (0 : ℝ)..(t : ℝ), hR.unforcedGradient δ hδ
        (R (Real.toNNReal (t-s)) (complexForceDrift Q i (hP.gradientOrbit f s)))) := by
  have he := congrArg (hR.unforcedGradient δ hδ) (hP.mild_duhamel hR f t)
  simpa only [map_add, map_smul, ← (hR.unforcedGradient δ hδ).intervalIntegral_comp_comm
    (hP.intervalIntegrable_mild_drift hR f t)] using he

private theorem tendsto_gradient_after
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (ht : 0 < t) {δ : ℕ → ℝ≥0} (hδ : ∀ n, 0 < δ n)
    (hδ0 : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n => hR.unforcedGradient (δ n) (hδ n) (R t f)) atTop
      (𝓝 (hR.gradientOrbit f (t : ℝ))) := by
  have hv : Tendsto (fun n =>
      (⟨δ n+t, add_pos_of_pos_of_nonneg (hδ n) t.property⟩ : {s : ℝ≥0 // 0 < s})) atTop
      (𝓝 (⟨t, ht⟩ : {s : ℝ≥0 // 0 < s})) := by
    apply tendsto_subtype_rng.mpr
    simpa only [zero_add] using hδ0.add_const t
  have hh := ((hR.continuous_unforcedGradient_apply f).tendsto ⟨t, ht⟩).comp hv
  have he : hR.unforcedGradient t ht f = hR.gradientOrbit f (t : ℝ) := by
    apply hR.unforcedGradient_eq
    simpa only [Real.toNNReal_coe] using hR.gradientOrbit_spec f
      (show (0 : ℝ) < (t : ℝ) from ht)
  rw [he] at hh
  apply hh.congr' (Eventually.of_forall fun n => ?_)
  exact congrArg (fun A => A f) (hR.unforcedGradient_add (δ n) (hδ n) t)

private theorem norm_regularized_integrand_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q))
    (δ : ℝ≥0) (hδ : 0 < δ) (t : ℝ≥0) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) t) :
    ‖hR.unforcedGradient δ hδ
      (R (Real.toNNReal (t-s)) (complexForceDrift Q i (hP.gradientOrbit f s)))‖ ≤
      (Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
          Real.exp (65 * complexForceShift d Λ₀ ζ * t) * ‖f‖)) *
        ((Real.sqrt s)⁻¹ * (Real.sqrt (t-s))⁻¹) := by
  let x := complexForceDrift Q i (hP.gradientOrbit f s)
  have hK : 0 ≤ Real.exp (2 * Λ₀) * Λ₀ :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)
  have ht : 0 < (t : ℝ)-s := sub_pos.mpr hs.2
  have he := congrArg (fun A => A x)
    (hR.unforcedGradient_add δ hδ (Real.toNNReal (t-s)))
  rw [ContinuousLinearMap.comp_apply] at he
  rw [← he]
  have hδτ : 0 < δ+Real.toNNReal (t-s) :=
    add_pos_of_pos_of_nonneg hδ (Real.toNNReal (t-s)).property
  have hb := ((hR.unforcedGradient (δ+Real.toNNReal (t-s)) hδτ).le_opNorm x).trans
    (mul_le_mul_of_nonneg_right (hR.norm_unforcedGradient_le _ hδτ) (norm_nonneg x))
  rw [NNReal.coe_add, Real.coe_toNNReal _ ht.le] at hb
  have hk : Real.sqrt ((Real.exp (2 * Λ₀) * Λ₀) / ((δ : ℝ)+(t-s))) ≤
      Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * (Real.sqrt (t-s))⁻¹ := by
    rw [← div_eq_mul_inv, ← Real.sqrt_div hK]
    exact Real.sqrt_le_sqrt (div_le_div_of_nonneg_left hK ht
      (le_add_of_nonneg_left δ.property))
  calc
    _ ≤ (Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * (Real.sqrt (t-s))⁻¹) *
        (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) * ‖hP.gradientOrbit f s‖) :=
      hb.trans (mul_le_mul hk (norm_complexForceDrift_apply_le Q i _) (norm_nonneg x)
        (by positivity))
    _ ≤ (Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * (Real.sqrt (t-s))⁻¹) *
        (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
          ((2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
            Real.exp (65 * complexForceShift d Λ₀ ζ * t) * ‖f‖) * (Real.sqrt s)⁻¹)) := by
      gcongr
      exact hP.norm_gradientOrbit_le f hs.1 hs.2.le
    _ = _ := by ring

private def regularization (n : ℕ) : ℝ≥0 := ((n : ℝ≥0)+1)⁻¹

private theorem regularization_pos (n : ℕ) : 0 < regularization n := by
  dsimp [regularization]
  positivity

private theorem regularization_zero : Tendsto regularization atTop (𝓝 0) := by
  simpa only [regularization, one_div] using!
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ≥0))

private theorem convolution_limit
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (ht : 0 < t) :
    IntervalIntegrable (hP.gradientDuhamelIntegrand hR f t) volume 0 t ∧
      Tendsto (fun n => ∫ s in (0 : ℝ)..(t : ℝ),
        hR.unforcedGradient (regularization n) (regularization_pos n)
          (R (Real.toNNReal (t-s)) (complexForceDrift Q i (hP.gradientOrbit f s)))) atTop
        (𝓝 (∫ s in (0 : ℝ)..(t : ℝ), hP.gradientDuhamelIntegrand hR f t s)) := by
  let F := fun (n : ℕ) (s : ℝ) => hR.unforcedGradient (regularization n) (regularization_pos n)
    (R (Real.toNNReal (t-s)) (complexForceDrift Q i (hP.gradientOrbit f s)))
  let C := Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
    (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      Real.exp (65 * complexForceShift d Λ₀ ζ * t) * ‖f‖)
  let bound := fun s : ℝ => C * ((Real.sqrt s)⁻¹ * (Real.sqrt (t-s))⁻¹)
  have hFm (n : ℕ) : AEStronglyMeasurable (F n) (volume.restrict (Ioc (0 : ℝ) t)) :=
    (hR.unforcedGradient (regularization n) (regularization_pos n)).continuous.comp_aestronglyMeasurable
      (hP.intervalIntegrable_mild_drift hR f t).aestronglyMeasurable
  have hlim : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) t →
      Tendsto (fun n => F n s) atTop (𝓝 (hP.gradientDuhamelIntegrand hR f t s)) := by
    filter_upwards [volume.ae_ne (t : ℝ)] with s hst hs
    have hst' : 0 < (t : ℝ)-s := sub_pos.mpr (lt_of_le_of_ne hs.2 hst)
    simpa only [IsComplexEnvironmentSemigroup.gradientDuhamelIntegrand,
      Real.coe_toNNReal _ hst'.le] using
      tendsto_gradient_after hR (complexForceDrift Q i (hP.gradientOrbit f s))
        (Real.toNNReal (t-s)) (by simpa using hst') regularization_pos regularization_zero
  have hbound (n : ℕ) : ∀ᵐ s ∂volume, s ∈ Ioc (0 : ℝ) t → ‖F n s‖ ≤ bound s := by
    filter_upwards [volume.ae_ne (t : ℝ)] with s hst hs
    exact norm_regularized_integrand_le hP hR f _ (regularization_pos n) t
      ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
  have hbi : IntervalIntegrable bound volume 0 t :=
    (intervalIntegrable_inv_sqrt_mul_inv_sqrt_sub (show (0 : ℝ) < (t : ℝ) from ht)).const_mul C
  have hlim' : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) t),
      Tendsto (fun n => F n s) atTop (𝓝 (hP.gradientDuhamelIntegrand hR f t s)) :=
    (ae_restrict_iff' measurableSet_Ioc).mpr hlim
  refine ⟨?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)]
    apply hbi.1.mono' (aestronglyMeasurable_of_tendsto_ae atTop hFm hlim')
    have hb := ae_all_iff.mpr hbound
    filter_upwards [hlim', ae_restrict_of_ae hb, ae_restrict_mem measurableSet_Ioc] with s hs hb hst
    exact le_of_tendsto hs.norm (Eventually.of_forall fun n => hb n hst)
  · apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence bound
    · apply Eventually.of_forall
      intro n
      rw [uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)]
      exact hFm n
    · exact Eventually.of_forall fun n => by
        simpa only [uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] using hbound n
    · exact hbi
    · simpa only [uIoc_of_le (show (0 : ℝ) ≤ (t : ℝ) from t.property)] using hlim

/-- The actual double-gradient Duhamel convolution is Bochner integrable on every positive horizon. -/
theorem IsComplexEnvironmentSemigroup.intervalIntegrable_mild_gradient_drift
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (ht : 0 < t) :
    IntervalIntegrable (hP.gradientDuhamelIntegrand hR f t) volume 0 t :=
  (convolution_limit hP hR f t ht).1

/-- Every complex L2 datum satisfies the actual unregularized horizontal-gradient Volterra identity. -/
theorem IsComplexEnvironmentSemigroup.gradient_mild_duhamel
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (ht : 0 < t) :
    hP.gradientOrbit f (t : ℝ) = hR.gradientOrbit f (t : ℝ) +
      ζ • (∫ s in (0 : ℝ)..(t : ℝ), hP.gradientDuhamelIntegrand hR f t s) := by
  let H := hR.gradientOrbit f (t : ℝ) +
    ζ • (∫ s in (0 : ℝ)..(t : ℝ), hP.gradientDuhamelIntegrand hR f t s)
  have hG : Tendsto (fun n => hR.unforcedGradient (regularization n) (regularization_pos n)
      (P t f)) atTop (𝓝 H) := by
    have hl := (tendsto_gradient_after hR f t ht regularization_pos regularization_zero).add
      ((convolution_limit hP hR f t ht).2.const_smul ζ)
    apply hl.congr' (Eventually.of_forall fun n => ?_)
    exact (hP.regularized_mild_gradient_duhamel hR f _ (regularization_pos n) t).symm
  have hu : Tendsto (fun n => R (regularization n) (P t f)) atTop (𝓝 (P t f)) := by
    simpa only [hR.1, ContinuousLinearMap.id_apply, Function.comp_def] using!
      ((hR.2.2.1 (P t f)).tendsto 0).comp regularization_zero
  have hH : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) (P t f) H := by
    letI := reducedLaw_probability Q
    apply complexHorizontalGradient_of_tendsto
      (Q := reducedLaw Q) (hQ := reducedLaw_stationary Q) (l := atTop)
      (p := fun n : ℕ => (R (regularization n) (P t f),
        (hR.unforcedGradient (regularization n) (regularization_pos n) (P t f)).ofLp))
      (q := (P t f, H.ofLp))
      (Eventually.of_forall fun n => hR.unforcedGradient_spec _ (regularization_pos n) (P t f))
    exact hu.prodMk_nhds
      ((PiLp.continuous_ofLp 2 (fun _ : Fin d => Lp ℂ 2 (reducedLaw Q))).tendsto H |>.comp hG)
  have hPt : HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q)
      (P t f) (hP.gradientOrbit f (t : ℝ)) := by
    simpa only [Real.toNNReal_coe] using hP.gradientOrbit_spec f
      (show (0 : ℝ) < (t : ℝ) from ht)
  exact WithLp.ofLp_injective 2 (hPt.unique hH)

/-- The actual gradient integrand has a uniform integrable double square-root majorant. -/
theorem IsComplexEnvironmentSemigroup.norm_gradientDuhamelIntegrand_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) t) :
    ‖hP.gradientDuhamelIntegrand hR f t s‖ ≤
      (Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
          Real.exp (65 * complexForceShift d Λ₀ ζ * t) * ‖f‖)) *
        ((Real.sqrt s)⁻¹ * (Real.sqrt (t-s))⁻¹) := by
  have hst : 0 < (t : ℝ)-s := sub_pos.mpr hs.2
  have hl := tendsto_gradient_after hR (complexForceDrift Q i (hP.gradientOrbit f s))
    (Real.toNNReal (t-s)) (by simpa using hst) regularization_pos regularization_zero
  rw [Real.coe_toNNReal _ hst.le] at hl
  exact le_of_tendsto hl.norm (Eventually.of_forall fun n =>
    norm_regularized_integrand_le hP hR f _ (regularization_pos n) t hs)

/-- Integrating the actual gradient convolution gives a time-uniform structural bound. -/
theorem IsComplexEnvironmentSemigroup.norm_integral_mild_gradient_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (f : Lp ℂ 2 (reducedLaw Q))
    (t : ℝ≥0) (ht : 0 < t) :
    ‖∫ s in (0 : ℝ)..(t : ℝ), hP.gradientDuhamelIntegrand hR f t s‖ ≤
      (8 * (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        Real.exp (65 * complexForceShift d Λ₀ ζ * t)) * ‖f‖ := by
  let C := Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
    (2 * Real.sqrt (Real.exp (2 * Λ₀) * Λ₀) *
      Real.exp (65 * complexForceShift d Λ₀ ζ * t) * ‖f‖)
  have hK : 0 ≤ Real.exp (2 * Λ₀) * Λ₀ :=
    mul_nonneg (Real.exp_pos _).le (zero_le_one.trans Q.ellipticity_parameter)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hi := intervalIntegrable_inv_sqrt_mul_inv_sqrt_sub (show (0 : ℝ) < (t : ℝ) from ht)
  calc
    _ ≤ ∫ s in (0 : ℝ)..(t : ℝ), C * ((Real.sqrt s)⁻¹ * (Real.sqrt (t-s))⁻¹) := by
      apply intervalIntegral.norm_integral_le_of_norm_le t.property ?_ (hi.const_mul C)
      filter_upwards [volume.ae_ne (t : ℝ)] with s hst hs
      exact hP.norm_gradientDuhamelIntegrand_le hR f t ⟨hs.1, lt_of_le_of_ne hs.2 hst⟩
    _ ≤ 4*C := by
      rw [intervalIntegral.integral_const_mul]
      exact (mul_le_mul_of_nonneg_left (integral_inv_sqrt_mul_inv_sqrt_sub_le
        (show (0 : ℝ) < (t : ℝ) from ht)) hC).trans_eq (mul_comm C 4)
    _ = _ := by
      calc
        4 * C =
            (8 * (Real.sqrt (Real.exp (2 * Λ₀) * Λ₀)) ^ 2 *
              ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
                Real.exp (65 * complexForceShift d Λ₀ ζ * t)) * ‖f‖ := by
          dsimp [C]
          ring
        _ = _ := by rw [Real.sq_sqrt hK]

/-- The actual forced/unforced positive-time gradient operators differ by O(abs(force)). -/
theorem IsComplexEnvironmentSemigroup.opNorm_gradient_sub_unforced_le
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hR : IsComplexEnvironmentSemigroup Q i 0 R) (t : ℝ≥0) (ht : 0 < t) :
    ‖hP.forcedGradient t ht - hR.unforcedGradient t ht‖ ≤
      8 * ‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        Real.exp (65 * complexForceShift d Λ₀ ζ * t) := by
  have hΛ : 0 ≤ Λ₀ := zero_le_one.trans Q.ellipticity_parameter
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro f
  have hPtf : hP.gradientOrbit f (t : ℝ) = hP.forcedGradient t ht f := by
    simp only [IsComplexEnvironmentSemigroup.gradientOrbit,
      dif_pos (show (0 : ℝ) < (t : ℝ) from ht), Real.toNNReal_coe]
  have hRtf : hR.gradientOrbit f (t : ℝ) = hR.unforcedGradient t ht f := by
    apply Eq.symm
    apply hR.unforcedGradient_eq
    simpa only [Real.toNNReal_coe] using hR.gradientOrbit_spec f
      (show (0 : ℝ) < (t : ℝ) from ht)
  change ‖hP.forcedGradient t ht f - hR.unforcedGradient t ht f‖ ≤ _
  rw [← hPtf, ← hRtf, hP.gradient_mild_duhamel hR f t ht, add_sub_cancel_left, norm_smul]
  calc
    _ ≤ ‖ζ‖ * ((8 * (Real.exp (2 * Λ₀) * Λ₀) * ((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀)) *
        Real.exp (65 * complexForceShift d Λ₀ ζ * t)) * ‖f‖) :=
      mul_le_mul_of_nonneg_left (hP.norm_integral_mild_gradient_le hR f t ht) (norm_nonneg ζ)
    _ = _ := by ring

end EinsteinFull
