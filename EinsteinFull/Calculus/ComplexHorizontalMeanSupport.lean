import EinsteinFull.Calculus.ComplexTranslationSupport
import EinsteinFull.Frozen.ComplexGeneratorGraph
import EinsteinFull.Frozen.ReducedLawProbability
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.Holder
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Mean cancellation for actual complex horizontal derivatives

The expectation-continuity argument adapts the real argument in the pinned
blueprint's `Correctors/HorizontalGeneratorMeanZero.lean` at revision
`7748a8e9000034825873768d309be8915ae53b07`. Constants are actual L2 classes,
not selected representatives. The generator conclusions use its frozen full
weak graph with the constant test function; no semigroup is assumed.
-/

open MeasureTheory Filter
open scoped Topology BigOperators

noncomputable section

namespace EinsteinFull

open EinsteinRelation

private def complexL2Integral {d : ℕ} (Q : Measure (FieldPair d)) [IsFiniteMeasure Q] :
    Lp ℂ 2 Q →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).lpPairing Q 2 2 (Lp.const 2 Q 1)

private theorem complexL2Integral_apply {d : ℕ} (Q : Measure (FieldPair d))
    [IsFiniteMeasure Q] (f : Lp ℂ 2 Q) :
    complexL2Integral Q f = ∫ ω, f ω ∂Q := by
  unfold complexL2Integral
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [Lp.coeFn_const 2 Q (1 : ℂ)] with ω hω
  simp only [hω, Function.const_apply, ContinuousLinearMap.mul_apply', one_mul]

/-- The Bochner integral of a complex L2 representative is continuous on a finite law. -/
theorem continuous_complexL2_integral {d : ℕ} (Q : Measure (FieldPair d))
    [IsFiniteMeasure Q] : Continuous (fun f : Lp ℂ 2 Q => ∫ ω, f ω ∂Q) := by
  have h : Continuous (fun f : Lp ℂ 2 Q => complexL2Integral Q f) :=
    (complexL2Integral Q).continuous
  simpa only [complexL2Integral_apply] using h

/-- Literal stationarity preserves the integral under actual complex translations. -/
theorem integral_complexTranslation {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) (f : Lp ℂ 2 Q) :
    (∫ ω, complexTranslation Q hQ x f ω ∂Q) = ∫ ω, f ω ∂Q := by
  rw [integral_congr_ae (coeFn_complexTranslation Q hQ x f)]
  have hmeas : AEMeasurable (translate x) Q :=
    (measurePreserving_translate Q hQ x).measurable.aemeasurable
  have hfm : AEStronglyMeasurable (⇑f) (Measure.map (translate x) Q) := by
    rw [hQ x]
    exact Lp.aestronglyMeasurable f
  rw [← integral_map hmeas hfm, hQ x]

/-- Every actual strong horizontal derivative has zero mean on a finite stationary law. -/
theorem HasComplexHorizontalDerivative.integral_eq_zero {d : ℕ}
    {Q : Measure (FieldPair d)} [IsFiniteMeasure Q] {hQ : IsStationary Q}
    {i : Fin d} {f g : Lp ℂ 2 Q} (hf : HasComplexHorizontalDerivative Q hQ i f g) :
    (∫ ω, g ω ∂Q) = 0 := by
  have hcomp := ((complexL2Integral Q).continuous.tendsto g).comp hf
  have hzero (t : ℝ) : complexL2Integral Q
      ((t : ℂ)⁻¹ • (complexTranslation Q hQ (t • unitVector i) f - f)) = 0 := by
    rw [map_smul, map_sub, complexL2Integral_apply, complexL2Integral_apply,
      integral_complexTranslation, sub_self, smul_zero]
  have hconst : Tendsto (fun t : ℝ => complexL2Integral Q
      ((t : ℂ)⁻¹ • (complexTranslation Q hQ (t • unitVector i) f - f)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℂ)) := by
    simp only [hzero]
    exact tendsto_const_nhds
  have hg : complexL2Integral Q g = 0 := tendsto_nhds_unique hcomp hconst
  simpa only [complexL2Integral_apply] using hg

/-- Actual translation fixes every constant L2 class. -/
theorem complexTranslation_const {d : ℕ} (Q : Measure (FieldPair d))
    [IsFiniteMeasure Q] (hQ : IsStationary Q) (x : Vec d) (c : ℂ) :
    complexTranslation Q hQ x (Lp.const 2 Q c) = Lp.const 2 Q c := by
  apply Lp.ext
  have hc := (measurePreserving_translate Q hQ x).quasiMeasurePreserving.ae
    (Lp.coeFn_const 2 Q c)
  filter_upwards [coeFn_complexTranslation Q hQ x (Lp.const 2 Q c),
    Lp.coeFn_const 2 Q c, hc] with ω ha hb hd
  simp only [ha, hd, hb, Function.const_apply]

/-- Constant L2 classes belong to the full horizontal H1 domain with zero gradient. -/
theorem hasComplexHorizontalGradient_const {d : ℕ} (Q : Measure (FieldPair d))
    [IsFiniteMeasure Q] (hQ : IsStationary Q) (c : ℂ) :
    HasComplexHorizontalGradient Q hQ (Lp.const 2 Q c) (fun _ => 0) := by
  intro i
  unfold HasComplexHorizontalDerivative
  simp only [complexTranslation_const, sub_self, smul_zero]
  exact tendsto_const_nhds

/-- Constant testing gives the exact mean balance of the full forced generator graph. -/
theorem IsComplexGeneratorPair.integral_eq {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i ζ f g) :
    ∃ Gf : Fin d → Lp ℂ 2 (reducedLaw Q),
      HasComplexHorizontalGradient (reducedLaw Q) (reducedLaw_stationary Q) f Gf ∧
      (∫ ω, g ω ∂reducedLaw Q) =
        ζ * (∫ ω, ∑ j, (ω.1 0 j i : ℂ) * Gf j ω ∂reducedLaw Q) := by
  letI := reducedLaw_probability Q
  obtain ⟨Gf, hGf, hw⟩ := hfg
  refine ⟨Gf, hGf, ?_⟩
  have htest := hw (Lp.const 2 (reducedLaw Q) 1) (fun _ => 0)
    (hasComplexHorizontalGradient_const (reducedLaw Q) (reducedLaw_stationary Q) 1)
  have hl : (∫ ω, g ω * Lp.const 2 (reducedLaw Q) 1 ω ∂reducedLaw Q) =
      ∫ ω, g ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
    simp only [hω, Function.const_apply, mul_one]
  have he : (∫ ω, ∑ j, ∑ k, (ω.1 0 j k : ℂ) * Gf k ω *
      (0 : Lp ℂ 2 (reducedLaw Q)) ω ∂reducedLaw Q) = 0 := by
    calc
      _ = ∫ _ : FieldPair d, (0 : ℂ) ∂reducedLaw Q := by
        apply integral_congr_ae
        filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
        simp only [hω, Pi.zero_apply, mul_zero, Finset.sum_const_zero]
      _ = 0 := integral_zero _ _
  have hr : (∫ ω, (∑ j, (ω.1 0 j i : ℂ) * Gf j ω) *
      Lp.const 2 (reducedLaw Q) 1 ω ∂reducedLaw Q) =
      ∫ ω, ∑ j, (ω.1 0 j i : ℂ) * Gf j ω ∂reducedLaw Q := by
    apply integral_congr_ae
    filter_upwards [Lp.coeFn_const 2 (reducedLaw Q) (1 : ℂ)] with ω hω
    simp only [hω, Function.const_apply, mul_one]
  simpa only [hl, he, hr, mul_zero, zero_add] using htest

/-- The actual unforced generator maps its domain into mean-zero L2 functions. -/
theorem IsComplexGeneratorPair.integral_eq_zero {d : ℕ} {Λ₀ r₀ : ℝ}
    {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d}
    {f g : Lp ℂ 2 (reducedLaw Q)} (hfg : IsComplexGeneratorPair Q i 0 f g) :
    (∫ ω, g ω ∂reducedLaw Q) = 0 := by
  obtain ⟨_, _, hmean⟩ := hfg.integral_eq
  simpa only [zero_mul] using hmean

end EinsteinFull
