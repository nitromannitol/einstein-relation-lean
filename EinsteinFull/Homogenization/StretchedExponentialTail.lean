import EinsteinRelation.External.AKMEnergyDensity
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Stretched-exponential moments from tail bounds

If `P[X ≥ t A] ≤ exp(-t^q)` for every `t ≥ 1` and `0 < s ≤ q`, then
`E[exp((X₊ / (8^(1/s) A))^s)] ≤ 2`, that is, `X ≤ O_s(8^(1/s) A)` in the notation of Armstrong,
Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Appendix A, (A.1). The proof is the layer-cake formula, as in the converse part of Lemma A.1
there; the tail is only used at levels `t ≥ 1`, the small levels being absorbed by the factor
`8^(1/s)`.
-/

open MeasureTheory Set

namespace EinsteinFull.Homogenization

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Layer-cake bound.** A nonnegative random variable `Z` with `P[Z > r] ≤ exp(-3r)` for every
`r ≥ 1/8` satisfies `E[exp Z] ≤ 2`. -/
theorem lintegral_ofReal_exp_le_two_of_tail [IsProbabilityMeasure μ] {Z : Ω → ℝ}
    (hZ : ∀ ω, 0 ≤ Z ω) (hm : AEMeasurable Z μ)
    (ht : ∀ r : ℝ, 1 / 8 ≤ r → μ {ω | r < Z ω} ≤ ENNReal.ofReal (Real.exp (-3 * r))) :
    ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω)) ∂μ ≤ 2 := by
  have hlayer := lintegral_comp_eq_lintegral_meas_lt_mul μ
    (f := Z) (g := Real.exp) (Filter.Eventually.of_forall hZ) hm
    (fun r _ => Real.continuous_exp.intervalIntegrable 0 r)
    (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
  set c : ENNReal := ENNReal.ofReal (Real.exp (1 / 8)) with hc
  have hdom : ∀ᵐ r ∂volume.restrict (Ioi (0 : ℝ)),
      μ {ω | r < Z ω} * ENNReal.ofReal (Real.exp r) ≤
        (Iio (1 / 8 : ℝ)).indicator (fun _ => c) r + ENNReal.ofReal (Real.exp (-2 * r)) := by
    refine Filter.Eventually.of_forall fun r => ?_
    by_cases hr : r < 1 / 8
    · rw [indicator_of_mem (show r ∈ Iio (1 / 8 : ℝ) from hr)]
      calc μ {ω | r < Z ω} * ENNReal.ofReal (Real.exp r) ≤ 1 * c :=
            mul_le_mul' prob_le_one (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hr.le))
        _ = c := one_mul c
        _ ≤ _ := le_self_add
    · rw [indicator_of_notMem (show r ∉ Iio (1 / 8 : ℝ) from hr), zero_add]
      calc μ {ω | r < Z ω} * ENNReal.ofReal (Real.exp r) ≤
            ENNReal.ofReal (Real.exp (-3 * r)) * ENNReal.ofReal (Real.exp r) :=
            mul_le_mul' (ht r (not_lt.mp hr)) le_rfl
        _ = ENNReal.ofReal (Real.exp (-2 * r)) := by
            rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
            congr 2
            ring
  have hg : IntegrableOn (fun r : ℝ => Real.exp (-2 * r)) (Ioi 0) :=
    integrableOn_exp_mul_Ioi (by norm_num) 0
  have hgL : ∫⁻ r in Ioi (0 : ℝ), ENNReal.ofReal (Real.exp (-2 * r)) = ENNReal.ofReal (1 / 2) := by
    rw [← ofReal_integral_eq_lintegral_ofReal hg
      (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le),
      integral_exp_mul_Ioi (by norm_num) 0]
    norm_num
  have hind : ∫⁻ r in Ioi (0 : ℝ), (Iio (1 / 8 : ℝ)).indicator (fun _ => c) r =
      c * ENNReal.ofReal (1 / 8) := by
    rw [lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio,
      Iio_inter_Ioi, Real.volume_Ioo, sub_zero]
  have he : Real.exp (1 / 8) ≤ 4 := by
    have h1 := Real.exp_one_lt_d9
    have h2 : Real.exp (1 / 8) ≤ Real.exp 1 := Real.exp_le_exp.mpr (by norm_num)
    linarith
  have hsum : ∫⁻ r in Ioi (0 : ℝ), ((Iio (1 / 8 : ℝ)).indicator (fun _ => c) r +
      ENNReal.ofReal (Real.exp (-2 * r))) ≤ 1 := by
    rw [lintegral_add_left (measurable_const.indicator measurableSet_Iio), hind, hgL, hc,
      ← ENNReal.ofReal_mul (Real.exp_pos _).le,
      ← ENNReal.ofReal_add (by positivity) (by norm_num), ← ENNReal.ofReal_one]
    refine ENNReal.ofReal_le_ofReal ?_
    linarith
  have hL : ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω) - 1) ∂μ ≤ 1 := by
    calc ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω) - 1) ∂μ
        = ∫⁻ ω, ENNReal.ofReal (∫ r in (0 : ℝ)..Z ω, Real.exp r) ∂μ := by
          refine lintegral_congr fun ω => ?_
          rw [integral_exp, Real.exp_zero]
      _ = _ := hlayer
      _ ≤ _ := lintegral_mono_ae hdom
      _ ≤ 1 := hsum
  have hpoint : ∀ ω, ENNReal.ofReal (Real.exp (Z ω)) =
      ENNReal.ofReal (Real.exp (Z ω) - 1) + 1 := by
    intro ω
    rw [← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add (by linarith [Real.one_le_exp (hZ ω)]) (by norm_num)]
    congr 1
    ring
  simp_rw [hpoint]
  rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
  calc ∫⁻ ω, ENNReal.ofReal (Real.exp (Z ω) - 1) ∂μ + 1 ≤ 1 + 1 := add_le_add hL le_rfl
    _ = 2 := one_add_one_eq_two

/-- **Stretched-exponential moments from a tail bound.** If `P[X ≥ t A] ≤ exp(-t^q)` for every
`t ≥ 1` and `0 < s ≤ q`, then `X ≤ O_s(8^(1/s) A)`. -/
theorem osBound_of_tail [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X)
    {s q A : ℝ} (hs : 0 < s) (hsq : s ≤ q) (hA : 0 < A)
    (htail : ∀ t : ℝ, 1 ≤ t → μ {ω | t * A ≤ X ω} ≤ ENNReal.ofReal (Real.exp (-(t ^ q)))) :
    EinsteinRelation.External.AKM.OsBound μ X s ((8 : ℝ) ^ s⁻¹ * A) := by
  have h8 : 0 < (8 : ℝ) ^ s⁻¹ := Real.rpow_pos_of_pos (by norm_num) _
  set θ := (8 : ℝ) ^ s⁻¹ * A with hθ
  have hθ0 : 0 < θ := mul_pos h8 hA
  refine ⟨hX, hs, hθ0, ?_⟩
  set Y : Ω → ℝ := fun ω => θ⁻¹ * max (X ω) 0 with hYdef
  have hY : ∀ ω, 0 ≤ Y ω := fun ω => mul_nonneg (inv_nonneg.mpr hθ0.le) (le_max_right _ _)
  refine lintegral_ofReal_exp_le_two_of_tail (Z := fun ω => Y ω ^ s)
    (fun ω => Real.rpow_nonneg (hY ω) _) ?_ ?_
  · exact (((hX.max measurable_const).const_mul _).pow_const _).aemeasurable
  · intro r hr
    have hr0 : 0 < r := by linarith
    have h8r : 1 ≤ 8 * r := by linarith
    set t := (8 * r) ^ s⁻¹ with ht
    have ht1 : 1 ≤ t := Real.one_le_rpow h8r (inv_nonneg.mpr hs.le)
    have htA : t * A = θ * r ^ s⁻¹ := by
      rw [ht, hθ, Real.mul_rpow (by norm_num) hr0.le]
      ring
    have hsub : {ω | r < Y ω ^ s} ⊆ {ω | t * A ≤ X ω} := by
      intro ω hω
      simp only [Set.mem_ofPred_eq] at hω ⊢
      have h1 : r ^ s⁻¹ < Y ω := by
        by_contra hcon
        push Not at hcon
        have h := Real.rpow_le_rpow (hY ω) hcon hs.le
        rw [Real.rpow_inv_rpow hr0.le hs.ne'] at h
        linarith
      have h2 : θ * r ^ s⁻¹ < max (X ω) 0 := by
        have h := mul_lt_mul_of_pos_left h1 hθ0
        rwa [hYdef, ← mul_assoc, mul_inv_cancel₀ hθ0.ne', one_mul] at h
      rcases lt_max_iff.mp h2 with h | h
      · rw [htA]
        exact h.le
      · exact absurd h (not_lt.mpr (by positivity))
    calc μ {ω | r < Y ω ^ s} ≤ μ {ω | t * A ≤ X ω} := measure_mono hsub
      _ ≤ ENNReal.ofReal (Real.exp (-(t ^ q))) := htail t ht1
      _ ≤ ENNReal.ofReal (Real.exp (-3 * r)) := by
          refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr ?_)
          have hq : t ^ q = (8 * r) ^ (q / s) := by
            rw [ht, ← Real.rpow_mul (by linarith), inv_mul_eq_div]
          have h3 : 8 * r ≤ (8 * r) ^ (q / s) := by
            calc 8 * r = (8 * r) ^ (1 : ℝ) := (Real.rpow_one _).symm
              _ ≤ (8 * r) ^ (q / s) :=
                Real.rpow_le_rpow_of_exponent_le h8r ((one_le_div hs).mpr hsq)
          rw [hq]
          linarith

end EinsteinFull.Homogenization
