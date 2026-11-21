import EinsteinFull.Homogenization.GaussianTestPairing
import EinsteinFull.Homogenization.HeatSelectedFluxPotential
import EinsteinFull.Homogenization.HeatFormulaMeasurability
import EinsteinRelation.Correctors.SpatialWeakLocalization

/-!
# Oscillation of the truncated heat potentials of a field with a pairing bound

Let `F` have a pairing bound at the scales above `R₀` with decay exponent `κ`. The time-truncated
heat gradient `W = ∫_τ^T ∂ᵢΦ_t * F dt` is estimated on the ball `B_r`, `r ≥ R₀`, in two
regimes. For `τ ≥ r²` its weak gradient is the truncated heat Hessian, which is bounded on `B_r`
by `C A R₀^κ r^(-κ) / κ`; the Poincaré inequality then bounds the oscillation of `W` on `B_r` by
`C A R₀^κ r^(1-κ) / κ` in normalized `L²`. For times between `λ r²` and `r²` the heat gradient
`∂ᵢΦ_t * F` is bounded on `B_r` by the pairing bound with Gaussian tests at the scale `r`, so
`|W| ≤ C A λ^(-(1+d/4)) r (r/R₀)^(-κ)` there. These are the intermediate- and large-time parts of
the proof of the flux corrector estimate (6.13) of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM

variable {d : ℕ}

theorem integral_euclideanSq_le_of_abs_le {G : Vec d → Vec d} {r b : ℝ}
    (hG : ∀ x ∈ ball (0 : Vec d) r, ∀ l, |G x l| ≤ b) :
    ∫ x in ball 0 r, euclideanSq (G x) ≤ d * b ^ 2 * volume.real (ball (0 : Vec d) r) := by
  have hfin := isFiniteMeasure_restrict_ball (d := d) r
  have h := integral_mono_of_nonneg (μ := volume.restrict (ball (0 : Vec d) r))
    (f := fun x => euclideanSq (G x)) (g := fun _ => (d : ℝ) * b ^ 2)
    (Filter.Eventually.of_forall fun x => _root_.Homogenization.vecNormSq_nonneg (G x))
    (integrable_const _) ?_
  · refine h.trans (le_of_eq ?_)
    rw [integral_const, smul_eq_mul, measureReal_def, measureReal_def,
      Measure.restrict_apply_univ]
    ring
  · filter_upwards [ae_restrict_mem (measurableSet_ball_zero r)] with x hx
    have hn := euclideanNorm_le_sqrt_mul_of_abs_le (hG x hx)
    rw [euclideanSq_eq_euclideanNorm_sq]
    calc euclideanNorm (G x) ^ 2 ≤ (Real.sqrt d * b) ^ 2 :=
          pow_le_pow_left₀ (euclideanNorm_nonneg _) hn 2
      _ = d * b ^ 2 := by rw [mul_pow, Real.sq_sqrt (Nat.cast_nonneg d)]

/-- The truncated heat Hessian of a field with a pairing bound is small at large times. -/
theorem exists_abs_heatHessianWindow_large_le (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Vec d → ℝ} {R₀ A κ : ℝ}, HasScalePairingBound F R₀ A κ →
      0 < R₀ → 0 ≤ A → 0 < κ → Measurable F → HasGaussianMoments F →
      ∀ (i l : Fin d) {τ T : ℝ}, R₀ ^ 2 ≤ τ → τ ≤ T → ∀ x : Vec d, euclideanNorm x ^ 2 ≤ τ →
        |heatHessianWindow τ T i l F x| ≤ C / κ * A * R₀ ^ κ * τ ^ (-(κ / 2)) := by
  obtain ⟨C₁, hC₁, hH⟩ := exists_heatHessianConv_le d
  refine ⟨2 * C₁, by positivity, ?_⟩
  intro F R₀ A κ hF hR₀ hA hκ hFm hmom i l τ T hτ hτT x hx
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hτ
  have hint : IntegrableOn (fun t : ℝ => C₁ * A * R₀ ^ κ * t ^ (-(1 + κ / 2))) (Icc τ T)
      volume := by
    have hc : ContinuousOn (fun t : ℝ => C₁ * A * R₀ ^ κ * t ^ (-(1 + κ / 2))) (Icc τ T) :=
      fun t ht => (continuousAt_const.mul (Real.continuousAt_rpow_const _ _ (Or.inl
        (lt_of_lt_of_le hτ0 ht.1).ne'))).continuousWithinAt
    exact hc.integrableOn_Icc
  unfold heatHessianWindow
  rw [← Real.norm_eq_abs]
  refine (norm_integral_le_of_norm_le hint ?_).trans ?_
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [Real.norm_eq_abs]
    exact hH hF hR₀ hA hκ.le hFm hmom i l t x (hτ.trans ht.1) (hx.trans ht.1)
  · rw [integral_const_mul]
    have h := setIntegral_rpow_neg_le hτ0 hτT (half_pos hκ)
    calc C₁ * A * R₀ ^ κ * ∫ t in Icc τ T, t ^ (-(1 + κ / 2))
        ≤ C₁ * A * R₀ ^ κ * (τ ^ (-(κ / 2)) / (κ / 2)) := by gcongr
      _ = 2 * C₁ / κ * A * R₀ ^ κ * τ ^ (-(κ / 2)) := by
          field_simp

/-- **Large-time oscillation of the truncated heat potential.** -/
theorem exists_osc_heatGradWindow_large_le (d : ℕ) (hd : 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : Vec d → ℝ} {R₀ A κ : ℝ}, HasScalePairingBound F R₀ A κ →
      0 < R₀ → 0 ≤ A → 0 < κ → Measurable F → HasGaussianMoments F →
      ∀ (i : Fin d) {r τ T : ℝ}, R₀ ≤ r → r ^ 2 ≤ τ → τ ≤ T →
        Real.sqrt (∫ x in ball 0 r, |heatGradWindow τ T i F x -
            ⨍ y in ball 0 r, heatGradWindow τ T i F y| ^ 2) ≤
          C / κ * A * R₀ ^ κ * r ^ (1 - κ) * Real.sqrt (volume.real (ball (0 : Vec d) r)) := by
  obtain ⟨C₁, hC₁, hH⟩ := exists_abs_heatHessianWindow_large_le d
  obtain ⟨CP, hCP, hP⟩ := EinsteinFull.ballPoincareEstimate_from_pde d hd
  refine ⟨CP * Real.sqrt d * C₁, by positivity, ?_⟩
  intro F R₀ A κ hF hR₀ hA hκ hFm hmom i r τ T hr hrτ hτT
  have hr0 : 0 < r := lt_of_lt_of_le hR₀ hr
  have hτ0 : 0 < τ := lt_of_lt_of_le (by positivity) hrτ
  have hR₀τ : R₀ ^ 2 ≤ τ := (pow_le_pow_left₀ hR₀.le hr 2).trans hrτ
  set W := heatGradWindow τ T i F with hW
  set H : Vec d → Vec d := fun x l => heatHessianWindow τ T i l F x with hHdef
  have hweak : HasWeakGradient (ball 0 r) W H :=
    hasWeakGradient_mono (subset_univ _)
      (fun l => hmom.hasWeakPartialDerivative_heatGradWindow hFm hτ0 hτT i l)
  have hWm : MemLp W 2 (volume.restrict (ball 0 r)) := hmom.memLp_heatGradWindow hτ0 hτT i hFm r
  have hHm : MemLp H 2 (volume.restrict (ball 0 r)) :=
    memLp_pi_iff.mpr fun l => hmom.memLp_heatHessianWindow hτ0 hτT i l hFm r
  have hPo := hP 0 r hr0 W H hWm hHm hweak
  set b := C₁ / κ * A * R₀ ^ κ * τ ^ (-(κ / 2)) with hb
  have hb0 : 0 ≤ b := by positivity
  have hbound : ∀ x ∈ ball (0 : Vec d) r, ∀ l, |H x l| ≤ b := by
    intro x hx l
    have hxr : euclideanNorm x < r := by
      have : euclideanNorm (x - 0) < r := hx
      rwa [sub_zero] at this
    have hx2 : euclideanNorm x ^ 2 ≤ τ :=
      (pow_le_pow_left₀ (euclideanNorm_nonneg x) hxr.le 2).trans hrτ
    exact hH hF hR₀ hA hκ hFm hmom i l hR₀τ hτT x hx2
  have hint := integral_euclideanSq_le_of_abs_le hbound
  have hτr : τ ^ (-(κ / 2)) ≤ r ^ (-κ) := by
    have h1 : (r ^ 2) ^ (-(κ / 2)) = r ^ (-κ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hr0.le]
      congr 1
      push_cast
      ring
    rw [← h1]
    exact Real.rpow_le_rpow_of_nonpos (by positivity) hrτ (by linarith)
  have hvol0 : 0 ≤ volume.real (ball (0 : Vec d) r) := measureReal_nonneg
  calc Real.sqrt (∫ x in ball 0 r, |W x - ⨍ y in ball 0 r, W y| ^ 2)
      ≤ CP * r * Real.sqrt (∫ x in ball 0 r, euclideanSq (H x)) := hPo
    _ ≤ CP * r * Real.sqrt (d * b ^ 2 * volume.real (ball (0 : Vec d) r)) := by
        gcongr
    _ = CP * r * (Real.sqrt d * b * Real.sqrt (volume.real (ball (0 : Vec d) r))) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (Nat.cast_nonneg d), Real.sqrt_sq hb0]
    _ ≤ CP * r * (Real.sqrt d * (C₁ / κ * A * R₀ ^ κ * r ^ (-κ)) *
          Real.sqrt (volume.real (ball (0 : Vec d) r))) := by
        rw [hb]
        gcongr
    _ = CP * Real.sqrt d * C₁ / κ * A * R₀ ^ κ * (r * r ^ (-κ)) *
          Real.sqrt (volume.real (ball (0 : Vec d) r)) := by ring
    _ = _ := by
        rw [show r * r ^ (-κ) = r ^ (1 - κ) by
          rw [sub_eq_add_neg, Real.rpow_add hr0, Real.rpow_one]]

end EinsteinFull.Homogenization
