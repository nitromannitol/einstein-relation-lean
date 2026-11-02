import EinsteinRelation.Calculus.HorizontalSobolev
import Mathlib.Analysis.Normed.Operator.Mul
import Mathlib.MeasureTheory.Function.Holder

/-! # Mean zero of the actual horizontal generator

Source `paper/main.tex:240–248`. On a stationary probability law, the L² generator of the
literal translation group in each coordinate has zero expectation. The expectation is the
continuous linear functional `h ↦ ∫ h dQ` on L², obtained as the Hölder pairing (exponents `2`
and `2`) of `h` with the constant one. Every translated difference quotient has mean zero by
literal stationarity, so the limit defining the generator has mean zero by uniqueness of real
limits. No core, density, conclusion, or paper estimate is assumed.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinRelation

/-- The expectation on `Lp ℝ 2 Q` of a probability law, as a continuous linear functional: the
Hölder pairing `ContinuousLinearMap.lpPairing` of multiplication (exponents `2`, `2`) with the
constant one. Its value is `∫ h * 1 dQ`, see `l2Expectation_apply`. -/
noncomputable def l2Expectation {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] :
    Lp ℝ 2 Q →L[ℝ] ℝ :=
  (ContinuousLinearMap.mul ℝ ℝ).lpPairing Q 2 2
    (MemLp.toLp (fun _ : FieldPair d => (1 : ℝ))
      (memLp_const (1 : ℝ) : MemLp (fun _ : FieldPair d => (1 : ℝ)) 2 Q))

/-- On a probability law, the L² expectation is the Bochner integral of the representative. -/
theorem l2Expectation_apply {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (h : Lp ℝ 2 Q) : l2Expectation Q h = ∫ ω, h ω ∂Q := by
  have hc : MemLp (fun _ : FieldPair d => (1 : ℝ)) 2 Q := memLp_const (1 : ℝ)
  unfold l2Expectation
  rw [ContinuousLinearMap.lpPairing_eq_integral]
  apply integral_congr_ae
  filter_upwards [MemLp.coeFn_toLp hc] with ω hω
  simp only [hω, ContinuousLinearMap.mul_apply', one_mul]

/-- Stationarity of the law makes the L² expectation invariant under every actual translation. -/
theorem l2Expectation_translationLp {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) (x : Vec d) (f : Lp ℝ 2 Q) :
    l2Expectation Q (translationLp Q hQ x f) = l2Expectation Q f := by
  rw [l2Expectation_apply Q, l2Expectation_apply Q]
  have hmeas : AEMeasurable (translate x) Q :=
    (measurePreserving_translate Q hQ x).measurable.aemeasurable
  have hfm : AEStronglyMeasurable (⇑f) (Measure.map (translate x) Q) := by
    rw [hQ x]
    exact Lp.aestronglyMeasurable f
  calc ∫ ω, (translationLp Q hQ x f) ω ∂Q = ∫ ω, f (translate x ω) ∂Q :=
        integral_congr_ae (coeFn_translationLp Q hQ x f)
    _ = ∫ ω, f ω ∂(Measure.map (translate x) Q) := (integral_map hmeas hfm).symm
    _ = ∫ ω, f ω ∂Q := by rw [hQ x]

/-- Source main.tex240–248: the coordinate generator of the actual L² translation group has
zero expectation on a stationary probability law. The proof uses only the strong difference
quotient limit, the continuity of the expectation, and literal stationarity. -/
theorem HasHorizontalLpDerivative.integral_eq_zero {d : ℕ} {Q : Measure (FieldPair d)}
    [IsProbabilityMeasure Q] {hQ : IsStationary Q} {i : Fin d} {f g : Lp ℝ 2 Q}
    (hf : HasHorizontalLpDerivative Q hQ i f g) : (∫ ω, g ω ∂Q) = 0 := by
  have hlim : Tendsto (fun t : ℝ => t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f))
      (𝓝[≠] (0 : ℝ)) (𝓝 g) := hf
  have hcomp : Tendsto
      (fun t : ℝ => l2Expectation Q (t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (l2Expectation Q g)) :=
    ((l2Expectation Q).continuous.tendsto g).comp hlim
  have hzero : ∀ t : ℝ,
      l2Expectation Q (t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f)) = 0 := by
    intro t
    rw [map_smul, map_sub, l2Expectation_translationLp Q hQ, sub_self, smul_zero]
  have hconst : Tendsto
      (fun t : ℝ => l2Expectation Q (t⁻¹ • (translationLp Q hQ (t • unitVector i) f - f)))
      (𝓝[≠] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
    simp only [hzero]
    exact tendsto_const_nhds
  have hg0 : l2Expectation Q g = 0 := tendsto_nhds_unique hcomp hconst
  rw [l2Expectation_apply Q] at hg0
  exact hg0

end EinsteinRelation
