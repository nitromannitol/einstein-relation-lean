import EinsteinRelation.Correctors.HeatTransferConvolution
import EinsteinRelation.Correctors.HeatTransferScales
import EinsteinRelation.Correctors.HeatConvolutionMeasurability
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Moment estimates for the heat-transfer formula

For Proposition 6.1, Step 2 (`paper/main.tex:1018–1031`), this file bounds both
terms of `K * H_T f - ∫₀ᵀ L * H_t f dt`, for an integrable signed spatial
kernel `K` and an integrable signed kernel `L` (eventually `L = ΔK`). The
time integral is shown to be absolutely convergent almost everywhere. No
time-integrated heat equation is assumed in these estimates.
-/

open MeasureTheory
open scoped ENNReal

noncomputable section

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- The literal right hand side of the heat-transfer identity
(`paper/main.tex:1020–1022`), with the second spatial kernel supplied explicitly.
The identity uses `L = ΔK`. -/
def heatTransferExpression (T : ℝ) (K L : Vec d → ℝ) (f : FieldPair d → ℝ)
    (ω : FieldPair d) : ℝ :=
  horizontalMollify K (heatSmoothed T f) ω -
    ∫ t in (0 : ℝ)..T, horizontalMollify L (heatSmoothed t f) ω

/-- Joint measurability of spatial convolution of a heat-smoothed field. -/
theorem measurable_horizontalMollify_heatSmoothed_joint
    {K : Vec d → ℝ} (hK : Measurable K) {f : FieldPair d → ℝ} (hf : Measurable f) :
    Measurable (fun z : ℝ × FieldPair d => horizontalMollify K (heatSmoothed z.1 f) z.2) := by
  have hj : Measurable (fun z : (ℝ × FieldPair d) × Vec d =>
      K z.2 * heatSmoothed z.1.1 f (translate z.2 z.1.2)) :=
    (hK.comp measurable_snd).mul
      ((measurable_heatSmoothed_joint hf).comp
        (measurable_fst.fst.prodMk
          (Probability.continuous_translate.measurable.comp
            (measurable_snd.prodMk measurable_fst.snd))))
  exact hj.stronglyMeasurable.integral_prod_right'.measurable

/-- Minkowski's inequality localized to a measurable integration set. -/
private theorem integral_moment_le_on
    {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    (Q : Measure Ω) [IsProbabilityMeasure Q] (ν : Measure X) [SigmaFinite ν]
    {m : ℝ} (hm : 1 ≤ m) {s : Set X} (hs : MeasurableSet s)
    {H : X → ℝ} (hH : Measurable H) (hH0 : ∀ x ∈ s, 0 ≤ H x)
    (hHi : IntegrableOn H s ν) {F : X × Ω → ℝ} (hF : Measurable F)
    (hFn : ∀ x ∈ s, MemLp (fun ω => F (x, ω)) (ENNReal.ofReal m) Q ∧
      eLpNorm (fun ω => F (x, ω)) (ENNReal.ofReal m) Q ≤ ENNReal.ofReal (H x)) :
    (∀ᵐ ω ∂Q, IntegrableOn (fun x => F (x, ω)) s ν) ∧
    MemLp (fun ω => ∫ x in s, F (x, ω) ∂ν) (ENNReal.ofReal m) Q ∧
    eLpNorm (fun ω => ∫ x in s, F (x, ω) ∂ν) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal (∫ x in s, H x ∂ν) := by
  classical
  let G : X × Ω → ℝ := fun z => if z.1 ∈ s then F z else 0
  have hG : Measurable G := Measurable.ite (measurable_fst hs) hF measurable_const
  have hGn : ∀ x, MemLp (fun ω => G (x, ω)) (ENNReal.ofReal m) Q ∧
      eLpNorm (fun ω => G (x, ω)) (ENNReal.ofReal m) Q ≤
        ENNReal.ofReal (s.indicator H x) := by
    intro x
    by_cases hx : x ∈ s
    · simpa only [G, if_pos hx, Set.indicator_of_mem hx] using hFn x hx
    · simp only [G, if_neg hx, Set.indicator_of_notMem hx]
      exact ⟨MemLp.zero, by simp⟩
  have h := integral_moment_le Q ν hm (s.indicator H) (hH.indicator hs)
    (fun x => by
      by_cases hx : x ∈ s
      · simpa only [Set.indicator_of_mem hx] using hH0 x hx
      · simp only [Set.indicator_of_notMem hx, le_refl])
    ((integrable_indicator_iff hs).mpr hHi) G hG hGn
  have hAE : ∀ᵐ ω ∂Q, IntegrableOn (fun x => F (x, ω)) s ν := by
    filter_upwards [h.1] with ω hω
    exact (integrable_indicator_iff hs).mp hω
  have hI : (fun ω => ∫ x, G (x, ω) ∂ν) = (fun ω => ∫ x in s, F (x, ω) ∂ν) :=
    funext fun ω => integral_indicator hs
  rw [hI, integral_indicator hs] at h
  exact ⟨hAE, h.2⟩

/-- The time-integrated spatial convolution has finite moments, with norm bounded
by `‖L‖₁ M ∫₀ᵀ ((1+t)^{-1/2}+R^{-1}) dt`. This proves the time-integral
estimate in `paper/main.tex:1025–1026` for the actual heat-smoothed field. -/
theorem integral_horizontalMollify_heatSmoothed_moment_le
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {m M R T : ℝ} (hm : 1 ≤ m) (hM : 0 ≤ M) (hR : 0 < R) (hT : 0 ≤ T)
    {L : Vec d → ℝ} (hL : Measurable L) (hLi : Integrable L)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfn : ∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal (M * heatAveragingProfile R t)) :
    (∀ᵐ ω ∂Q, IntervalIntegrable
      (fun t => horizontalMollify L (heatSmoothed t f) ω) volume 0 T) ∧
    MemLp (fun ω => ∫ t in (0 : ℝ)..T, horizontalMollify L (heatSmoothed t f) ω)
      (ENNReal.ofReal m) Q ∧
    eLpNorm (fun ω => ∫ t in (0 : ℝ)..T, horizontalMollify L (heatSmoothed t f) ω)
      (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal ((∫ x, |L x|) * M *
        (∫ t in (0 : ℝ)..T, heatAveragingProfile R t)) := by
  have hprof : Measurable (heatAveragingProfile R) := by
    unfold heatAveragingProfile
    fun_prop
  have hbound : ∀ t ∈ Set.Ioc (0 : ℝ) T,
      MemLp (horizontalMollify L (heatSmoothed t f)) (ENNReal.ofReal m) Q ∧
      eLpNorm (horizontalMollify L (heatSmoothed t f)) (ENNReal.ofReal m) Q ≤
        ENNReal.ofReal ((∫ x, |L x|) * M * heatAveragingProfile R t) := by
    intro t ht
    have hft : Measurable (heatSmoothed t f) :=
      (measurable_heatSmoothed_joint hf).comp (measurable_const.prodMk measurable_id)
    have h := (horizontalMollify_moment_le Q hQ hm
      (mul_nonneg hM (heatAveragingProfile_nonneg hR t)) hL hLi hft (hfn t ht.1.le)).2
    simpa only [mul_assoc] using h
  have h := integral_moment_le_on Q volume hm measurableSet_Ioc
    (hprof.const_mul ((∫ x, |L x|) * M))
    (fun t _ => mul_nonneg (mul_nonneg (integral_nonneg fun x => abs_nonneg (L x)) hM)
      (heatAveragingProfile_nonneg hR t))
    (((intervalIntegrable_heatAveragingProfile R hT).const_mul
      ((∫ x, |L x|) * M)).1)
    (measurable_horizontalMollify_heatSmoothed_joint hL hf) hbound
  have hAE : ∀ᵐ ω ∂Q, IntervalIntegrable
      (fun t => horizontalMollify L (heatSmoothed t f) ω) volume 0 T := by
    filter_upwards [h.1] with ω hω
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mpr hω
  simpa only [← intervalIntegral.integral_of_le hT, intervalIntegral.integral_const_mul] using
    And.intro hAE h.2

/-- Moment bound for both terms on the right of the heat-transfer formula in
`paper/main.tex:1020–1026`. This is an estimate on the explicit expression; the
identification with `K * f` is a separate time-integrated heat equation. -/
theorem heat_transfer_moment_le
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    {m M R T : ℝ} (hm : 1 ≤ m) (hM : 0 ≤ M) (hR : 0 < R) (hT : 0 ≤ T)
    {K L : Vec d → ℝ} (hK : Measurable K) (hKi : Integrable K)
    (hL : Measurable L) (hLi : Integrable L)
    {f : FieldPair d → ℝ} (hf : Measurable f)
    (hfn : ∀ t : ℝ, 0 ≤ t → eLpNorm (heatSmoothed t f) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal (M * heatAveragingProfile R t)) :
    MemLp (fun ω => horizontalMollify K (heatSmoothed T f) ω -
      ∫ t in (0 : ℝ)..T, horizontalMollify L (heatSmoothed t f) ω) (ENNReal.ofReal m) Q ∧
    eLpNorm (fun ω => horizontalMollify K (heatSmoothed T f) ω -
      ∫ t in (0 : ℝ)..T, horizontalMollify L (heatSmoothed t f) ω) (ENNReal.ofReal m) Q ≤
      ENNReal.ofReal ((∫ x, |K x|) * M * heatAveragingProfile R T +
        (∫ x, |L x|) * M * (∫ t in (0 : ℝ)..T, heatAveragingProfile R t)) := by
  have hft : Measurable (heatSmoothed T f) :=
    (measurable_heatSmoothed_joint hf).comp (measurable_const.prodMk measurable_id)
  have h₁ := (horizontalMollify_moment_le Q hQ hm
    (mul_nonneg hM (heatAveragingProfile_nonneg hR T)) hK hKi hft (hfn T hT)).2
  have h₂ := (integral_horizontalMollify_heatSmoothed_moment_le
    Q hQ hm hM hR hT hL hLi hf hfn).2
  refine ⟨h₁.1.sub h₂.1, ?_⟩
  calc
    _ ≤ eLpNorm (horizontalMollify K (heatSmoothed T f)) (ENNReal.ofReal m) Q +
        eLpNorm (fun ω => ∫ t in (0 : ℝ)..T, horizontalMollify L (heatSmoothed t f) ω)
          (ENNReal.ofReal m) Q :=
      eLpNorm_sub_le (f := horizontalMollify K (heatSmoothed T f))
        (g := fun ω => ∫ t in (0 : ℝ)..T, horizontalMollify L (heatSmoothed t f) ω)
        (ENNReal.one_le_ofReal.mpr hm)
    _ ≤ ENNReal.ofReal ((∫ x, |K x|) * (M * heatAveragingProfile R T)) +
        ENNReal.ofReal ((∫ x, |L x|) * M *
          (∫ t in (0 : ℝ)..T, heatAveragingProfile R t)) := add_le_add h₁.2 h₂.2
    _ = _ := by
      rw [← ENNReal.ofReal_add (mul_nonneg (integral_nonneg fun x => abs_nonneg (K x))
        (mul_nonneg hM (heatAveragingProfile_nonneg hR T))) (by
        exact mul_nonneg (mul_nonneg (integral_nonneg fun x => abs_nonneg (L x)) hM)
          (intervalIntegral.integral_nonneg hT fun t _ => heatAveragingProfile_nonneg hR t))]
      simp only [mul_assoc]

end EinsteinRelation.Correctors
