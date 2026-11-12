import EinsteinRelation.Correctors.SpecifiedFlowAllCentersGradient
import EinsteinRelation.Correctors.AKMActualColumnInitialMoments
import EinsteinRelation.Correctors.AKMActualSemigroupGradientTail
import EinsteinRelation.Correctors.AKMRealTranslation

/-! # All-center decay and tails of a specified canonical column flow

Source: `paper/main.tex:798–816,850–857`. The actual coefficient regularity
supplies the uniform scalar bound, while the scalar large-time moments
remain an explicit internal obligation on this same flow. No additional
literature predicate or change of gradient witness is used.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Sharp gradient decay at all centers and the literal unit-ball time tail
for the same prescribed canonical flow. Only the scalar late-time profile
remains to be supplied by canonical identification with the source flow.
Source: `paper/main.tex:798–816,850–857`. -/
theorem actualCoefficientLaw_same_canonical_flow_gradient_decay_and_tail
    (hreg : ParabolicLargeScale) (d : ℕ) (hd : 2 ≤ d)
    (L r₀ : ℝ) (hL : 1 ≤ L) :
    ∃ J : ℝ → ℝ, (∀ m : ℝ, 2 ≤ m → 0 < J m) ∧
      ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d)
        (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
        (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
        Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
          (ℝ × Vec d) => u z.1 z.2) →
        Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
          (ℝ × Vec d) => G z.1 z.2) →
        (∀ᵐ A ∂actualCoefficientLaw Q,
          IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
          HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
        (∀ᵐ A ∂actualCoefficientLaw Q, ∀ t : ℝ, 0 < t →
          HasWeakGradient univ (fun x => u A (t,x)) (fun x => G A (t,x))) →
        ∀ F : ℝ → ℝ, (∀ m : ℝ, 0 < m → 0 < F m) →
        (∀ m : ℝ, 0 < m → ∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
          MemLp (fun A => u A (t,x)) (ENNReal.ofReal m) (actualCoefficientLaw Q) ∧
          eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal m) (actualCoefficientLaw Q) ≤
            ENNReal.ofReal (F m*t^(-(1 : ℝ)/2-(d : ℝ)/4))) →
        let C := fun m => J m*((d : ℝ)*akmColumnLipschitzConstant d L r₀ + F (2*m))
        (∀ (v : Vec d) (m t : ℝ), 2 ≤ m → 1 ≤ t →
          MemLp (fun A => vectorRms volume (originBall d 1) (fun x => G A (t,v+x)))
            (ENNReal.ofReal m) (actualCoefficientLaw Q) ∧
          eLpNorm (fun A => vectorRms volume (originBall d 1) (fun x => G A (t,v+x)))
            (ENNReal.ofReal m) (actualCoefficientLaw Q) ≤
              ENNReal.ofReal (C m*t^(-1-(d : ℝ)/4))) ∧
        ∀ (m T : ℝ), 2 ≤ m → 1 ≤ T →
          MemLp (fun A => vectorRms volume (originBall d 1)
            (fun x => ∫ t in Ioi T, G A (t,x))) (ENNReal.ofReal m) (actualCoefficientLaw Q) ∧
          eLpNorm (fun A => vectorRms volume (originBall d 1)
            (fun x => ∫ t in Ioi T, G A (t,x))) (ENNReal.ofReal m) (actualCoefficientLaw Q) ≤
              ENNReal.ofReal ((C m/((d : ℝ)/4))*T^(-((d : ℝ)/4))) := by
  obtain ⟨J,hJ,hgradient⟩ := specifiedSemigroupFlow_bounded_gradient_decay_all_centers
    hreg d hd (AKMUpperEllipticity L) 1 (one_lt_AKMUpperEllipticity hL)
      (by norm_num) (by norm_num)
  refine ⟨J,hJ,?_⟩
  intro Q i u G hum hGm hflow hweak F hF hscalar
  have hB : 0 ≤ (d : ℝ)*akmColumnLipschitzConstant d L r₀ := by positivity
  have hgrad := hgradient (actualCoefficientLaw Q) (isAdmissibleLaw_actualCoefficientLaw Q)
    (measurePreserving_actualCoefficientTranslation Q) _ u G hum hGm
    (hflow.mono fun _ h => h.1) hweak _ hB
    (ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow) F hF hscalar
  refine ⟨hgrad,?_⟩
  intro m T hm hT
  have hC : 0 < J m*((d : ℝ)*akmColumnLipschitzConstant d L r₀ + F (2*m)) :=
    mul_pos (hJ m hm) (add_pos_of_nonneg_of_pos hB (hF _ (by linarith only [hm])))
  apply actualCoefficientLaw_semigroup_gradient_ball_tail_moment_le
    (by omega) Q i u G hGm (hflow.mono fun _ h => h.1)
    (ENNReal.one_le_ofReal.mpr (one_le_two.trans hm)) ENNReal.ofReal_ne_top
    hC (zero_lt_one.trans_le hT) zero_lt_one
  intro t ht
  simpa only [zero_add] using (hgrad 0 m t hm (hT.trans ht.le)).2

end EinsteinRelation.Correctors
