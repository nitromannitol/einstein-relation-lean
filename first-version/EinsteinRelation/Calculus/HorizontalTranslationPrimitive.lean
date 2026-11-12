import EinsteinRelation.Calculus.WeakCalculusAlgebra
import EinsteinRelation.Correctors.HorizontalGeneratorsIbP
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! # Primitives of the actual translation group

Source: `paper/main.tex:1021–1029`. Integrating a stationary field along
a finite translation segment gives a primitive of its translation difference.
This is an ingredient of the compact small-scale residual flux.
-/

open MeasureTheory Filter
open scoped Topology

noncomputable section

namespace EinsteinRelation

variable {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]

/-- A segment integral of the strongly continuous horizontal translation
group has derivative equal to the endpoint difference
(`paper/main.tex:1021–1029`). The field being integrated need only be in `L²`. -/
theorem hasHorizontalLpDerivative_translationPrimitive (hQ : IsStationary Q)
    (i : Fin d) (b : ℝ) (X : Lp ℝ 2 Q) :
    HasHorizontalLpDerivative Q hQ i
      (∫ t in (0 : ℝ)..b, translationLp Q hQ (t • unitVector i) X)
      (translationLp Q hQ (b • unitVector i) X - X) := by
  let G : ℝ → Lp ℝ 2 Q := fun t => translationLp Q hQ (t • unitVector i) X
  have hG : Continuous G := (continuous_translationLp Q hQ).comp
    ((continuous_id.smul continuous_const).prodMk continuous_const)
  have hGi (a c : ℝ) : IntervalIntegrable G volume a c := hG.intervalIntegrable a c
  let Y : Lp ℝ 2 Q := ∫ t in (0 : ℝ)..b, G t
  have hshift (a : ℝ) : translationLp Q hQ (a • unitVector i) Y =
      (∫ t in (0 : ℝ)..(b + a), G t) - ∫ t in (0 : ℝ)..a, G t := by
    change (translationLp Q hQ (a • unitVector i)).toContinuousLinearMap
      (∫ t in (0 : ℝ)..b, G t) = _
    rw [← (translationLp Q hQ (a • unitVector i)).toContinuousLinearMap.intervalIntegral_comp_comm
      (hGi 0 b)]
    change (∫ t in (0 : ℝ)..b, translationLp Q hQ (a • unitVector i) (G t)) = _
    have heq : (fun t => translationLp Q hQ (a • unitVector i) (G t)) =
        fun t => G (t + a) := by
      funext t
      dsimp only [G]
      rw [add_smul, translationLp_add, translationLp_comm]
    rw [heq, intervalIntegral.integral_comp_add_right]
    simp only [zero_add]
    exact eq_sub_of_add_eq' (intervalIntegral.integral_add_adjacent_intervals
      (hGi 0 a) (hGi a (b + a)))
  have hb := intervalIntegral.integral_hasDerivAt_right (hGi 0 b)
    hG.stronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt
  have hzero := intervalIntegral.integral_hasDerivAt_right (hGi 0 0)
    hG.stronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt
  have hderiv : HasDerivAt (fun a : ℝ => translationLp Q hQ (a • unitVector i) Y)
      (G b - G 0) (0 : ℝ) := by
    have hb' : HasDerivAt (fun u => ∫ t in (0 : ℝ)..u, G t)
        (G (b + 0)) (b + 0) := by simpa only [add_zero] using hb
    have htop := hb'.scomp (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).const_add b)
    have h := htop.sub hzero
    simpa only [one_smul, add_zero, Function.comp_def, hshift] using h
  have hslope : slope (fun a => translationLp Q hQ (a • unitVector i) Y) 0 =
      fun a : ℝ => a⁻¹ • (translationLp Q hQ (a • unitVector i) Y - Y) := by
    funext a
    simp only [slope_def_module, sub_zero, zero_smul, translationLp_zero]
  rw [hasDerivAt_iff_tendsto_slope, hslope] at hderiv
  simpa only [G, zero_smul, translationLp_zero] using hderiv

omit [IsProbabilityMeasure Q] in
/-- The translation primitive costs only the length of its segment
(`paper/main.tex:1028–1029`). -/
theorem norm_translationPrimitive_le (hQ : IsStationary Q)
    (i : Fin d) (b : ℝ) (X : Lp ℝ 2 Q) :
    ‖∫ t in (0 : ℝ)..b, translationLp Q hQ (t • unitVector i) X‖ ≤ |b| * ‖X‖ := by
  have h := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := b) (C := ‖X‖)
    (f := fun t => translationLp Q hQ (t • unitVector i) X)
    (fun t _ => (norm_translationLp Q hQ _ X).le)
  simpa only [sub_zero, mul_comm ‖X‖] using h

/-- A coordinate translation difference is the full weak divergence of
its segment primitive (`paper/main.tex:1021–1029`). The displayed source
uses the canonical `L²` endpoint representatives. -/
theorem hasWeakHorizontalDivergence_translationPrimitive (hQ : IsStationary Q)
    (i : Fin d) (b : ℝ) (X : Lp ℝ 2 Q) :
    let Y := ∫ t in (0 : ℝ)..b, translationLp Q hQ (t • unitVector i) X
    HasWeakHorizontalDivergence Q hQ (fun ω => Pi.single i (Y ω))
      (fun ω => (translationLp Q hQ (b • unitVector i) X) ω - X ω) := by
  classical
  dsimp only
  let Y := ∫ t in (0 : ℝ)..b, translationLp Q hQ (t • unitVector i) X
  let Z := translationLp Q hQ (b • unitVector i) X
  have hY : Integrable (fun ω => Y ω) Q := (Lp.memLp Y).integrable one_le_two
  have hZ : Integrable (fun ω => Z ω - X ω) Q :=
    ((Lp.memLp Z).integrable one_le_two).sub ((Lp.memLp X).integrable one_le_two)
  refine ⟨fun j => ?_, hZ, fun F _ DF hDF => ?_⟩
  · by_cases hj : i = j
    · subst j
      simpa only [Pi.single_eq_same] using hY
    · simpa only [Pi.single_eq_of_ne (Ne.symm hj)] using
        (integrable_zero (FieldPair d) ℝ Q)
  · have h := (Correctors.horizontalGenerators_integration_by_parts Q hQ i Y (Z - X) F (DF i)
      (hasHorizontalLpDerivative_translationPrimitive hQ i b X) (hDF i)).2.2
    have hsrc : (∫ ω, (Z - X) ω * F ω ∂Q) = ∫ ω, (Z ω - X ω) * F ω ∂Q := by
      apply integral_congr_ae
      filter_upwards [Lp.coeFn_sub Z X] with ω hω
      rw [hω]
      rfl
    rw [hsrc] at h
    have hleft : (∫ ω, ∑ j : Fin d, (Pi.single i (Y ω) : Vec d) j * DF j ω ∂Q) =
        ∫ ω, Y ω * DF i ω ∂Q := by
      congr 1
      funext ω
      simp [Pi.single_apply]
    rw [hleft]
    linarith only [h]

end EinsteinRelation
