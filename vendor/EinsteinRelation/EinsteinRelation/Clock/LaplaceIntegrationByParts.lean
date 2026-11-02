import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Integration by parts in time for a bounded Laplace transform

For a measurable bounded `g : ℝ → ℝ` and `s > 0`,
`s ∫₀^∞ e^{-st} g(t) dt = s² ∫₀^∞ e^{-st} (∫₀ᵗ g(u) du) dt`.

The right-hand side is an iterated integral of the kernel
`1_{0 < u < t} e^{-st} g(u)` on `ℝ × ℝ`. Fubini's theorem swaps the order of
integration; the `t`-integral of the swapped form is `e^{-su} / s`.
Integrability of the kernel uses only the bound `|g| ≤ M`: the `u`-integral of
its absolute value is at most `M t e^{-st}`, which is integrable on `(0, ∞)`.
Continuity of `g` is not used.
-/

namespace EinsteinRelation.Clock

open MeasureTheory

/-- A scalar factor times a quantity bounded by `M` is bounded by the factor times `M`. -/
private lemma laplace_norm_mul_le {c x M : ℝ} (hc : 0 ≤ c) (hx : |x| ≤ M) :
    ‖c * x‖ ≤ c * M := by
  rw [norm_mul, Real.norm_of_nonneg hc, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left hx hc

/-- The kernel `1_{0 < u < t} e^{-st} g(u)` on the `u`-slice for fixed `t`. -/
private lemma laplace_kernel_slice_u (s : ℝ) (g : ℝ → ℝ) (t u : ℝ) :
    Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
        (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)
      = Set.indicator (Set.Ioo 0 t) (fun u => Real.exp (-(s * t)) * g u) u := by
  by_cases h : 0 < u ∧ u < t
  · have h1 : (t, u) ∈ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} := show 0 < u ∧ u < t from h
    have h2 : u ∈ Set.Ioo 0 t := h
    simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  · have h1 : (t, u) ∉ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} :=
      fun hm => h (show 0 < u ∧ u < t from hm)
    have h2 : u ∉ Set.Ioo 0 t := h
    simp only [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

/-- The kernel on the `t`-slice for fixed `u > 0`. -/
private lemma laplace_kernel_slice_t (s : ℝ) (g : ℝ → ℝ) {u : ℝ} (hu : 0 < u) (t : ℝ) :
    Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
        (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)
      = Set.indicator (Set.Ioi u) (fun t => Real.exp (-(s * t)) * g u) t := by
  by_cases h : u < t
  · have h1 : (t, u) ∈ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} :=
      show 0 < u ∧ u < t from ⟨hu, h⟩
    have h2 : t ∈ Set.Ioi u := h
    simp only [Set.indicator_of_mem h1, Set.indicator_of_mem h2]
  · have h1 : (t, u) ∉ {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} :=
      fun hm => h (show 0 < u ∧ u < t from hm).2
    have h2 : t ∉ Set.Ioi u := h
    simp only [Set.indicator_of_notMem h1, Set.indicator_of_notMem h2]

/-- The kernel vanishes when `t ≤ 0` or `u ≤ 0`. -/
private lemma laplace_kernel_eq_zero (s : ℝ) (g : ℝ → ℝ) (t u : ℝ) (h : t ≤ 0 ∨ u ≤ 0) :
    Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
        (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u) = 0 := by
  refine Set.indicator_of_notMem ?_ _
  intro hm
  have hm' : 0 < u ∧ u < t := hm
  rcases h with h | h <;> linarith [hm'.1, hm'.2]

/-- The function `t ↦ t e^{-st}` is integrable on `(0, ∞)`. -/
private lemma laplace_integrableOn_mul_exp {s : ℝ} (hs : 0 < s) :
    IntegrableOn (fun t : ℝ => t * Real.exp (-(s * t))) (Set.Ioi 0) := by
  have h : IntegrableOn (fun x : ℝ => x ^ (1 : ℝ) * Real.exp (-s * x ^ (1 : ℝ))) (Set.Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) zero_lt_one hs
  simpa only [Real.rpow_one, neg_mul] using h

/-- The tail integral `∫_{u}^{∞} e^{-st} dt` equals `e^{-su} / s`. -/
private lemma laplace_integral_exp_Ioi {s : ℝ} (hs : 0 < s) (u : ℝ) :
    ∫ t in Set.Ioi u, Real.exp (-(s * t)) = Real.exp (-(s * u)) / s := by
  have h := integral_exp_mul_Ioi (a := -s) (by linarith) u
  simpa only [neg_mul, neg_div_neg_eq] using h

/-- Intervals `(0, t)` have finite Lebesgue measure. -/
private lemma laplace_volume_Ioo_ne_top (t : ℝ) : volume (Set.Ioo (0 : ℝ) t) ≠ ⊤ := by
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_ne_top

/-- The kernel `(t, u) ↦ 1_{0 < u < t} e^{-st} g(u)` is integrable on `ℝ × ℝ`. -/
private lemma laplace_kernel_integrable (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ)
    (hM : ∀ t, |g t| ≤ M) {s : ℝ} (hs : 0 < s) :
    Integrable (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
        (fun p => Real.exp (-(s * p.1)) * g p.2) p)
      ((volume : Measure ℝ).prod (volume : Measure ℝ)) := by
  have hS1 : MeasurableSet {p : ℝ × ℝ | 0 < p.2} :=
    measurableSet_lt (measurable_const : Measurable fun _ : ℝ × ℝ => (0 : ℝ)) measurable_snd
  have hS2 : MeasurableSet {p : ℝ × ℝ | p.2 < p.1} :=
    measurableSet_lt measurable_snd measurable_fst
  have hS : MeasurableSet {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} := by
    first
      | exact hS1.inter hS2
      | rw [Set.setOf_and]; exact hS1.inter hS2
  have hEc : Continuous (fun p : ℝ × ℝ => Real.exp (-(s * p.1))) := by
    have h1 : Continuous (fun p : ℝ × ℝ => -(s * p.1)) :=
      ((continuous_const : Continuous fun _ : ℝ × ℝ => s).mul continuous_fst).neg
    exact Real.continuous_exp.comp h1
  have hKm : Measurable (fun p : ℝ × ℝ => Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
      (fun p => Real.exp (-(s * p.1)) * g p.2) p) :=
    (hEc.measurable.mul (hg.comp measurable_snd)).indicator hS
  -- Each `u`-slice is integrable: it is a bounded function supported in `(0, t)`.
  have hu_int : ∀ t : ℝ, Integrable (fun u : ℝ => Set.indicator
      {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)) volume := by
    intro t
    have hbdd : IntegrableOn (fun u : ℝ => Real.exp (-(s * t)) * g u) (Set.Ioo 0 t) :=
      MeasureTheory.Measure.integrableOn_of_bounded (M := Real.exp (-(s * t)) * M)
        (laplace_volume_Ioo_ne_top t)
        (hg.const_mul (Real.exp (-(s * t)))).aestronglyMeasurable
        (ae_of_all _ fun u => laplace_norm_mul_le (Real.exp_pos (-(s * t))).le (hM u))
    refine (hbdd.integrable_indicator measurableSet_Ioo).congr (ae_of_all _ fun u => ?_)
    exact (laplace_kernel_slice_u s g t u).symm
  have hconst : ∀ t : ℝ, Integrable (fun u : ℝ => Set.indicator (Set.Ioo 0 t)
      (fun _ : ℝ => Real.exp (-(s * t)) * M) u) volume := fun t =>
    ((integrableOn_const (laplace_volume_Ioo_ne_top t) enorm_ne_top :
      IntegrableOn (fun _ : ℝ => Real.exp (-(s * t)) * M) (Set.Ioo 0 t))).integrable_indicator
      measurableSet_Ioo
  have hvol : ∀ t : ℝ, 0 < t →
      ∫ u, Set.indicator (Set.Ioo 0 t) (fun _ : ℝ => Real.exp (-(s * t)) * M) u
        = M * (t * Real.exp (-(s * t))) := by
    intro t ht
    rw [MeasureTheory.integral_indicator_const _ measurableSet_Ioo,
      Real.volume_real_Ioo_of_le ht.le, smul_eq_mul]
    ring
  -- Pointwise bound of the kernel's absolute value by `e^{-st} M` on `(0, t)`.
  have hnorm_pt : ∀ t u : ℝ, ‖Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
      (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)‖
        ≤ Set.indicator (Set.Ioo 0 t) (fun _ : ℝ => Real.exp (-(s * t)) * M) u := by
    intro t u
    rw [laplace_kernel_slice_u s g t u]
    by_cases h : u ∈ Set.Ioo 0 t
    · simp only [Set.indicator_of_mem h]
      exact laplace_norm_mul_le (Real.exp_pos (-(s * t))).le (hM u)
    · simp only [Set.indicator_of_notMem h, norm_zero, le_refl]
  -- Bound of the `u`-integral of the absolute value by `M t e^{-st}`.
  have hbound : ∀ t : ℝ, ∫ u, ‖Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
      (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)‖
        ≤ Set.indicator (Set.Ioi (0 : ℝ)) (fun t => M * (t * Real.exp (-(s * t)))) t := by
    intro t
    by_cases ht : 0 < t
    · rw [Set.indicator_of_mem (show t ∈ Set.Ioi (0 : ℝ) from ht)]
      have hmono : ∫ u, ‖Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
          (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)‖
            ≤ ∫ u, Set.indicator (Set.Ioo 0 t) (fun _ : ℝ => Real.exp (-(s * t)) * M) u :=
        integral_mono_of_nonneg (ae_of_all _ fun u => norm_nonneg _) (hconst t)
          (ae_of_all _ fun u => hnorm_pt t u)
      exact hmono.trans (hvol t ht).le
    · rw [Set.indicator_of_notMem (show t ∉ Set.Ioi (0 : ℝ) from ht)]
      have h0 : ∀ u : ℝ, Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
          (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u) = 0 :=
        fun u => laplace_kernel_eq_zero s g t u (Or.inl (not_lt.mp (show ¬ (0 : ℝ) < t from ht)))
      simp only [h0, norm_zero, MeasureTheory.integral_zero, le_refl]
  have hψ : Integrable (fun t : ℝ => Set.indicator (Set.Ioi (0 : ℝ))
      (fun t => M * (t * Real.exp (-(s * t)))) t) volume := by
    refine (integrable_indicator_iff measurableSet_Ioi).mpr ?_
    exact Integrable.const_mul (laplace_integrableOn_mul_exp hs) M
  have hmarg : AEStronglyMeasurable (fun t : ℝ => ∫ u, ‖Set.indicator
      {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1} (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)‖) volume :=
    (hKm.norm.stronglyMeasurable.integral_prod_right').aestronglyMeasurable
  refine (integrable_prod_iff hKm.aestronglyMeasurable).mpr ⟨ae_of_all _ fun t => hu_int t, ?_⟩
  refine hψ.mono' hmarg (ae_of_all _ fun t => ?_)
  have hpos : 0 ≤ ∫ u, ‖Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
      (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)‖ :=
    integral_nonneg fun u => norm_nonneg _
  exact (Real.norm_of_nonneg hpos).le.trans (hbound t)

/-- Integration by parts in time for the bounded Laplace transform: for a bounded measurable
`g` and `s > 0`, `s` times the Laplace transform of `g` equals `s²` times the Laplace
transform of its running integral `t ↦ ∫₀ᵗ g`. -/
theorem laplace_eq_laplace_primitive (g : ℝ → ℝ) (hg : Measurable g) (M : ℝ) (hM : ∀ t, |g t| ≤ M) {s : ℝ} (hs : 0 < s) :
    s * ∫ t in Set.Ioi (0:ℝ), Real.exp (-(s * t)) * g t
      = s ^ 2 * ∫ t in Set.Ioi (0:ℝ), Real.exp (-(s * t)) * ∫ u in (0:ℝ)..t, g u := by
  have hsne : s ≠ 0 := hs.ne'
  have hK := laplace_kernel_integrable g hg M hM hs
  -- For `t > 0` the `u`-integral of the kernel is `e^{-st} ∫₀ᵗ g`.
  have hslice_t : ∀ t : ℝ, t ∈ Set.Ioi (0 : ℝ) →
      Real.exp (-(s * t)) * (∫ u in (0 : ℝ)..t, g u)
        = ∫ u, Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
            (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u) := by
    intro t ht
    have ht' : 0 < t := ht
    calc Real.exp (-(s * t)) * (∫ u in (0 : ℝ)..t, g u)
        = Real.exp (-(s * t)) * (∫ u in Set.Ioo 0 t, g u) := by
          rw [intervalIntegral.integral_of_le ht'.le, MeasureTheory.integral_Ioc_eq_integral_Ioo]
      _ = ∫ u in Set.Ioo 0 t, Real.exp (-(s * t)) * g u :=
          (MeasureTheory.integral_const_mul _ _).symm
      _ = ∫ u, Set.indicator (Set.Ioo 0 t) (fun u => Real.exp (-(s * t)) * g u) u :=
          (MeasureTheory.integral_indicator measurableSet_Ioo).symm
      _ = ∫ u, Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
            (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u) :=
          MeasureTheory.integral_congr_ae (ae_of_all _ fun u => (laplace_kernel_slice_u s g t u).symm)
  -- For `t ≤ 0` the `u`-integral of the kernel vanishes.
  have hzero_t : ∀ t : ℝ, t ∉ Set.Ioi (0 : ℝ) →
      ∫ u, Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
        (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u) = 0 := by
    intro t ht
    have ht' : t ≤ 0 := not_lt.mp (show ¬ (0 : ℝ) < t from ht)
    have h0 : ∀ u : ℝ, Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
        (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u) = 0 :=
      fun u => laplace_kernel_eq_zero s g t u (Or.inl ht')
    simp only [h0, MeasureTheory.integral_zero]
  have hR : (∫ t in Set.Ioi (0 : ℝ), Real.exp (-(s * t)) * (∫ u in (0 : ℝ)..t, g u))
      = ∫ t, ∫ u, Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
          (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u) :=
    (MeasureTheory.setIntegral_congr_fun measurableSet_Ioi fun t ht => hslice_t t ht).trans
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero_t)
  -- Fubini: swap the order of integration of the kernel.
  have hswap : ∫ t, ∫ u, Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
        (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)
      = ∫ u, ∫ t, Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
          (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u) :=
    MeasureTheory.integral_integral_swap
      (f := fun t u => Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
        (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)) hK
  -- For `u > 0` the `t`-integral of the kernel is `e^{-su} g(u) / s`.
  have hinner_pos : ∀ u : ℝ, 0 < u →
      ∫ t, Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
          (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)
        = Real.exp (-(s * u)) * g u * s⁻¹ := by
    intro u hu
    have hpt : ∀ t : ℝ, Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
        (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)
        = Set.indicator (Set.Ioi u) (fun t => Real.exp (-(s * t)) * g u) t :=
      fun t => laplace_kernel_slice_t s g hu t
    simp only [hpt]
    rw [MeasureTheory.integral_indicator measurableSet_Ioi, MeasureTheory.integral_mul_const,
      laplace_integral_exp_Ioi hs u]
    ring
  have hinner : ∀ u : ℝ, ∫ t, Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
        (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u)
      = Set.indicator (Set.Ioi (0 : ℝ)) (fun u => Real.exp (-(s * u)) * g u * s⁻¹) u := by
    intro u
    by_cases hu : 0 < u
    · rw [Set.indicator_of_mem (show u ∈ Set.Ioi (0 : ℝ) from hu)]
      exact hinner_pos u hu
    · rw [Set.indicator_of_notMem (show u ∉ Set.Ioi (0 : ℝ) from hu)]
      have h0 : ∀ t : ℝ, Set.indicator {p : ℝ × ℝ | 0 < p.2 ∧ p.2 < p.1}
          (fun p => Real.exp (-(s * p.1)) * g p.2) (t, u) = 0 :=
        fun t => laplace_kernel_eq_zero s g t u (Or.inr (not_lt.mp hu))
      simp only [h0, MeasureTheory.integral_zero]
  have hinv : s * s⁻¹ = 1 := mul_inv_cancel₀ hsne
  have key : ∀ x : ℝ, s * x = s ^ 2 * (x * s⁻¹) := by
    intro x
    calc s * x = s * x * (s * s⁻¹) := by rw [hinv, mul_one]
      _ = s ^ 2 * (x * s⁻¹) := by ring
  rw [hR, hswap]
  simp only [hinner]
  rw [MeasureTheory.integral_indicator measurableSet_Ioi, MeasureTheory.integral_mul_const]
  exact key _

end EinsteinRelation.Clock
