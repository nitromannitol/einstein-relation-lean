import EinsteinRelation.Probability.LaplaceMoments
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Prod

/-! # Laplace-weighted occupation transfer

This file carries the step from the time-integrated occupation bound to the
exponentially weighted bound in `paper/main.tex` Proposition 3.2
(`regen.occupation-time` to `regen.occupation-resolvent`, lines 439–447).

If `∫_{[0,T]} g ≤ C (T + λ⁻²) M` for every `T > 0`, then
`∫_{[0,∞)} s e^{-st} g(t) dt ≤ C (1 + s λ⁻²) M`.

The proof writes the exponential weight as a superposition of tail integrals,
`s e^{-st} = ∫_{[t,∞)} s² e^{-sT} dT`, exchanges the two integrations by Tonelli,
and evaluates the two Laplace moments of the resulting `T`-density.

Time is real-valued (`ℝ≥0` carries no measure space at the pinned Mathlib version),
and every time integral runs over `Set.Ici 0` or `Set.Icc 0 T`.
-/

open MeasureTheory Set

namespace EinsteinRelation

/-- Algebra of the tail kernel: `s² · (-e / -s) = s · e` for `s ≠ 0`. -/
theorem laplace_tail_algebra (s e : ℝ) (hs : s ≠ 0) :
    s ^ 2 * (-e / -s) = s * e := by
  rw [neg_div_neg_eq, div_eq_mul_inv]
  calc s ^ 2 * (e * s⁻¹) = s * e * (s * s⁻¹) := by ring
    _ = s * e := by rw [mul_inv_cancel₀ hs, mul_one]

/-- An integrable function on `(a, ∞)` is integrable on `[a, ∞)`. -/
theorem laplace_integrableOn_Ici_of_Ioi {F : ℝ → ℝ} {a : ℝ} (h : IntegrableOn F (Ioi a)) :
    IntegrableOn F (Ici a) := by
  have hae : Ioi a =ᵐ[volume] Ici a := Ioi_ae_eq_Ici' (measure_singleton a)
  exact h.congr_set_ae hae.symm

/-- The exponential `e^{-sT}` is integrable on `(0, ∞)`. -/
theorem laplace_integrableOn_exp (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun T : ℝ => Real.exp (-s * T)) (Ioi 0) :=
  integrableOn_exp_mul_Ioi (a := -s) (by linarith) 0

/-- `T e^{-sT}` is integrable on `(0, ∞)`. A nonzero Laplace moment forces integrability,
since a non-integrable integrand has zero integral. -/
theorem laplace_integrableOn_tExp (s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun T : ℝ => T * Real.exp (-s * T)) (Ioi 0) := by
  by_contra hnot
  have h0 : ∫ T in Ioi (0 : ℝ), T * Real.exp (-s * T) = 0 := integral_undef hnot
  have h1 := EinsteinRelation.Probability.laplace_first_moment s hs
  rw [h0, mul_zero] at h1
  exact zero_ne_one h1

/-- The tail integral of the Laplace time density: `∫_{[t,∞)} s² e^{-sT} dT = s e^{-st}`. -/
theorem laplace_tail_lintegral (s t : ℝ) (hs : 0 < s) :
    ∫⁻ T in Ici t, ENNReal.ofReal (s ^ 2 * Real.exp (-s * T)) =
      ENNReal.ofReal (s * Real.exp (-s * t)) := by
  have hI : IntegrableOn (fun T : ℝ => s ^ 2 * Real.exp (-s * T)) (Ici t) :=
    laplace_integrableOn_Ici_of_Ioi
      (Integrable.const_mul (integrableOn_exp_mul_Ioi (a := -s) (by linarith) t) (s ^ 2))
  have hnn : ∀ᵐ T ∂(volume.restrict (Ici t)), 0 ≤ s ^ 2 * Real.exp (-s * T) :=
    ae_of_all _ fun T => by positivity
  rw [← ofReal_integral_eq_lintegral_ofReal hI hnn]
  congr 1
  rw [integral_const_mul, integral_Ici_eq_integral_Ioi,
    integral_exp_mul_Ioi (by linarith : -s < 0) t]
  exact laplace_tail_algebra s _ hs.ne'

/-- Splitting the weighted occupation integrand into two Laplace moments. -/
theorem laplace_integrand_split (lam C s : ℝ) :
    (fun T : ℝ => s ^ 2 * Real.exp (-s * T) * (C * (T + (lam ^ 2)⁻¹))) =
      fun T : ℝ => C * (s ^ 2 * (T * Real.exp (-s * T))) +
        (C * (s ^ 2 * (lam ^ 2)⁻¹)) * Real.exp (-s * T) := by
  funext T
  ring

/-- The weighted occupation integrand is integrable on `[0, ∞)`. -/
theorem laplace_integrableOn_integrand (lam C s : ℝ) (hs : 0 < s) :
    IntegrableOn (fun T : ℝ => s ^ 2 * Real.exp (-s * T) * (C * (T + (lam ^ 2)⁻¹)))
      (Ici 0) := by
  refine laplace_integrableOn_Ici_of_Ioi ?_
  rw [laplace_integrand_split lam C s]
  exact Integrable.add''
    (Integrable.const_mul (Integrable.const_mul (laplace_integrableOn_tExp s hs) (s ^ 2)) C)
    (Integrable.const_mul (laplace_integrableOn_exp s hs) (C * (s ^ 2 * (lam ^ 2)⁻¹)))

/-- The weighted occupation integral over `[0, ∞)` equals `C (1 + s λ⁻²)`. -/
theorem laplace_integral_value (lam C s : ℝ) (hs : 0 < s) :
    ∫ T in Ici (0 : ℝ), s ^ 2 * Real.exp (-s * T) * (C * (T + (lam ^ 2)⁻¹)) =
      C * (1 + s * (lam ^ 2)⁻¹) := by
  have hv1 : s ^ 2 * (∫ T in Ioi (0 : ℝ), T * Real.exp (-s * T)) = 1 :=
    EinsteinRelation.Probability.laplace_first_moment s hs
  have hv0 : s * (∫ T in Ioi (0 : ℝ), Real.exp (-s * T)) = 1 :=
    EinsteinRelation.Probability.laplace_mass s hs
  rw [integral_Ici_eq_integral_Ioi, laplace_integrand_split lam C s,
    integral_add
      (Integrable.const_mul (Integrable.const_mul (laplace_integrableOn_tExp s hs) (s ^ 2)) C)
      (Integrable.const_mul (laplace_integrableOn_exp s hs) (C * (s ^ 2 * (lam ^ 2)⁻¹)))]
  simp only [integral_const_mul]
  linear_combination C * hv1 + C * (lam ^ 2)⁻¹ * s * hv0

/-- Tonelli inner step, left side: for `t ≥ 0`, integrating the indicator `{t ≤ T}`
against `T` over `[0, ∞)` gives the tail integral from `t`. -/
theorem laplace_inner_left (φ g : ℝ → ENNReal) (hφ : Measurable φ) (t : ℝ) (ht : 0 ≤ t) :
    ∫⁻ T in Ici (0 : ℝ), (if t ≤ T then φ T * g t else 0) =
      (∫⁻ T in Ici t, φ T) * g t := by
  have hind : ∀ T : ℝ, (if t ≤ T then φ T * g t else 0) =
      (Ici t).indicator (fun T => φ T * g t) T := by
    intro T
    by_cases h : t ≤ T
    · rw [if_pos h, Set.indicator_of_mem (show T ∈ Ici t from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show T ∉ Ici t from h)]
  rw [lintegral_congr hind, lintegral_indicator measurableSet_Ici,
    Measure.restrict_restrict measurableSet_Ici,
    Set.inter_eq_left.2 (Set.Ici_subset_Ici.2 ht)]
  exact lintegral_mul_const (g t) hφ

/-- Tonelli inner step, right side: for fixed `T`, integrating the indicator `{t ≤ T}`
against `t` over `[0, ∞)` gives the integral of `g` over `[0, T]`. -/
theorem laplace_inner_right (φ g : ℝ → ENNReal) (hg : Measurable g) (T : ℝ) :
    ∫⁻ t in Ici (0 : ℝ), (if t ≤ T then φ T * g t else 0) =
      φ T * ∫⁻ t in Icc (0 : ℝ) T, g t := by
  have hind : ∀ t : ℝ, (if t ≤ T then φ T * g t else 0) =
      (Iic T).indicator (fun t => φ T * g t) t := by
    intro t
    by_cases h : t ≤ T
    · rw [if_pos h, Set.indicator_of_mem (show t ∈ Iic T from h)]
    · rw [if_neg h, Set.indicator_of_notMem (show t ∉ Iic T from h)]
  rw [lintegral_congr hind, lintegral_indicator measurableSet_Iic,
    Measure.restrict_restrict measurableSet_Iic, Set.inter_comm, Set.Ici_inter_Iic]
  exact lintegral_const_mul (φ T) hg

/-- Tonelli exchange for the tail representation of the exponential weight. -/
theorem laplace_tonelli (φ g : ℝ → ENNReal) (hφ : Measurable φ) (hg : Measurable g) :
    ∫⁻ t in Ici (0 : ℝ), (∫⁻ T in Ici t, φ T) * g t =
      ∫⁻ T in Ici (0 : ℝ), φ T * ∫⁻ t in Icc (0 : ℝ) T, g t := by
  have hm : Measurable (fun p : ℝ × ℝ => if p.1 ≤ p.2 then φ p.2 * g p.1 else 0) :=
    Measurable.ite (measurableSet_le measurable_fst measurable_snd)
      ((hφ.comp measurable_snd).mul (hg.comp measurable_fst)) measurable_const
  calc ∫⁻ t in Ici (0 : ℝ), (∫⁻ T in Ici t, φ T) * g t
      = ∫⁻ t in Ici (0 : ℝ), ∫⁻ T in Ici (0 : ℝ), (if t ≤ T then φ T * g t else 0) := by
        refine lintegral_congr_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
        exact (laplace_inner_left φ g hφ t (Set.mem_Ici.1 ht)).symm
    _ = ∫⁻ T in Ici (0 : ℝ), ∫⁻ t in Ici (0 : ℝ), (if t ≤ T then φ T * g t else 0) :=
        lintegral_lintegral_swap (f := fun t T => if t ≤ T then φ T * g t else 0)
          hm.aemeasurable
    _ = ∫⁻ T in Ici (0 : ℝ), φ T * ∫⁻ t in Icc (0 : ℝ) T, g t :=
        lintegral_congr fun T => laplace_inner_right φ g hg T

/-- Proposition 3.2 (`regen.occupation-resolvent`) in the time variable `t ∈ [0, ∞)`:
an occupation bound on every `[0, T]` transfers to the exponentially weighted occupation. -/
theorem laplace_occupation_transfer (lam C : ℝ) (M : ENNReal) (hlam : 0 < lam) (hC : 0 ≤ C)
    (g : ℝ → ENNReal) (hg : Measurable g)
    (hocc : ∀ T : ℝ, 0 < T →
      ∫⁻ t in Icc (0 : ℝ) T, g t ≤ ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) * M)
    (s : ℝ) (hs : 0 < s) :
    ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (s * Real.exp (-s * t)) * g t ≤
      ENNReal.ofReal (C * (1 + s * (lam ^ 2)⁻¹)) * M := by
  have hinv : 0 < (lam ^ 2)⁻¹ := inv_pos.2 (pow_pos hlam 2)
  have hcont₁ : Continuous (fun T : ℝ => s ^ 2 * Real.exp (-s * T)) := by fun_prop
  have hcont₂ : Continuous (fun T : ℝ => s ^ 2 * Real.exp (-s * T) * (C * (T + (lam ^ 2)⁻¹))) := by
    fun_prop
  have hφm : Measurable (fun T : ℝ => ENNReal.ofReal (s ^ 2 * Real.exp (-s * T))) :=
    hcont₁.measurable.ennreal_ofReal
  have hfm : Measurable (fun T : ℝ =>
      ENNReal.ofReal (s ^ 2 * Real.exp (-s * T) * (C * (T + (lam ^ 2)⁻¹)))) :=
    hcont₂.measurable.ennreal_ofReal
  have hfnn : ∀ᵐ T ∂(volume.restrict (Ici (0 : ℝ))),
      0 ≤ s ^ 2 * Real.exp (-s * T) * (C * (T + (lam ^ 2)⁻¹)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ici] with T hT
    exact mul_nonneg (by positivity) (mul_nonneg hC (add_nonneg (Set.mem_Ici.1 hT) hinv.le))
  have hpos : ∀ᵐ T ∂(volume.restrict (Ici (0 : ℝ))), 0 < T := by
    have hae : Ioi (0 : ℝ) =ᵐ[volume] Ici 0 := Ioi_ae_eq_Ici' (measure_singleton 0)
    rw [← Measure.restrict_congr_set hae]
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with T hT
    exact Set.mem_Ioi.1 hT
  calc ∫⁻ t in Ici (0 : ℝ), ENNReal.ofReal (s * Real.exp (-s * t)) * g t
      = ∫⁻ t in Ici (0 : ℝ), (∫⁻ T in Ici t, ENNReal.ofReal (s ^ 2 * Real.exp (-s * T))) * g t := by
        refine lintegral_congr fun t => ?_
        rw [laplace_tail_lintegral s t hs]
    _ = ∫⁻ T in Ici (0 : ℝ), ENNReal.ofReal (s ^ 2 * Real.exp (-s * T)) *
          ∫⁻ t in Icc (0 : ℝ) T, g t :=
        laplace_tonelli (fun T => ENNReal.ofReal (s ^ 2 * Real.exp (-s * T))) g hφm hg
    _ ≤ ∫⁻ T in Ici (0 : ℝ), ENNReal.ofReal (s ^ 2 * Real.exp (-s * T)) *
          (ENNReal.ofReal (C * (T + (lam ^ 2)⁻¹)) * M) := by
        refine lintegral_mono_ae ?_
        filter_upwards [hpos] with T hT
        exact mul_le_mul_of_nonneg_left (hocc T hT) zero_le
    _ = ∫⁻ T in Ici (0 : ℝ),
          ENNReal.ofReal (s ^ 2 * Real.exp (-s * T) * (C * (T + (lam ^ 2)⁻¹))) * M := by
        refine lintegral_congr fun T => ?_
        rw [ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ s ^ 2 * Real.exp (-s * T))]
        ring
    _ = (∫⁻ T in Ici (0 : ℝ),
          ENNReal.ofReal (s ^ 2 * Real.exp (-s * T) * (C * (T + (lam ^ 2)⁻¹)))) * M :=
        lintegral_mul_const M hfm
    _ = ENNReal.ofReal (∫ T in Ici (0 : ℝ),
          s ^ 2 * Real.exp (-s * T) * (C * (T + (lam ^ 2)⁻¹))) * M := by
        rw [ofReal_integral_eq_lintegral_ofReal (laplace_integrableOn_integrand lam C s hs) hfnn]
    _ = ENNReal.ofReal (C * (1 + s * (lam ^ 2)⁻¹)) * M := by
        rw [laplace_integral_value lam C s hs]

end EinsteinRelation
