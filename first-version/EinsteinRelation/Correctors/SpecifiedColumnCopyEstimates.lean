import EinsteinRelation.Correctors.AKMCanonicalColumnScalarDecay
import EinsteinRelation.Correctors.AKMSpecifiedCanonicalGradientTail
import EinsteinRelation.Correctors.RecenteredCopyDoubleBallGradientDecay

/-! # Specified canonical flow estimates for the conditional-copy argument

Source: `paper/main.tex:777–808,826–849,878–886`. The frozen kernel-flow
decay applies directly to the supplied canonical flow. Both the late-time
gradient tail and the finite-time paired estimate retain that same flow.
Construction of a jointly measurable flow and its identification with the
stationary corrector remain separate internal obligations.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM ReductionImageV3 Environment.AKMTestIntegralSupport
open NormalizedSpatialRepresentativeSupport

/-- Sharp gradient decay at every center and the literal infinite-time
unit-ball remainder for a specified canonical column. The kernel version
of AKM Theorem 9.1 discharges the scalar decay premise without selecting
another flow. Source: `paper/main.tex:790–808,842–849`. -/
theorem canonical_column_gradient_decay_and_tail
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (d : ℕ) (hd : 2 ≤ d) (L r₀ : ℝ) (hL : 1 ≤ L) :
    ∃ C : ℝ → ℝ, (∀ m : ℝ, 2 ≤ m → 0 < C m) ∧
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
  obtain ⟨F, hF, hscalar⟩ := parabolicSemigroupKernelDecay_canonical_column_moments
    hdecay d hd (AKMUpperEllipticity L) 1 (one_lt_AKMUpperEllipticity hL)
      (by norm_num) (by norm_num)
  obtain ⟨J, hJ, hbound⟩ := actualCoefficientLaw_same_canonical_flow_gradient_decay_and_tail
    hreg d hd L r₀ hL
  refine ⟨fun m => J m*((d : ℝ)*akmColumnLipschitzConstant d L r₀ + F (2*m)), ?_, ?_⟩
  · intro m hm
    have hB : 0 ≤ (d : ℝ)*akmColumnLipschitzConstant d L r₀ := by positivity
    exact mul_pos (hJ m hm) (add_pos_of_nonneg_of_pos hB (hF _ (by linarith)))
  intro Q i u G hum hGm hflow hweak
  exact hbound Q i u G hum hGm hflow hweak F hF
    (hscalar (actualCoefficientLaw Q) (isAdmissibleLaw_actualCoefficientLaw Q)
      i u G hum hflow)

/-- Sharp finite-time paired gradient decay on the manuscript's double
ball under the actual recentered physical copy law. The scalar literature
estimate and cutoff exponent are discharged. The single constant precedes
the law, column, flow, radius, and center.
Source: `paper/main.tex:826–849,878–886`. -/
theorem recenteredPhysicalCopy_doubleBall_integrated_gradient_decay_of_kernelDecay
    (hdecay : ParabolicSemigroupKernelDecay)
    (d : ℕ) (hd : 2 ≤ d) (L r₀ m : ℝ) (hL : 1 ≤ L) (hm : 2 ≤ m) :
    ∃ B : ℝ, 0 < B ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
      (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => G z.1 z.2) →
      (∀ᵐ A ∂actualCoefficientLaw Q,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
      ∀ R : ℝ, 1 ≤ R → ∀ y : Point d,
      let F := fun A : PhysicalField d L × PhysicalField d L =>
        vectorRms volume (originBall d (2*R))
          (fun x => ∫ t in Icc (0 : ℝ) (4*R^2),
            G (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) -
              G (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x))
      MemLp F (ENNReal.ofReal m) (recenteredPhysicalCopyLaw Q (r₀*R) y) ∧
        eLpNorm F (ENNReal.ofReal m) (recenteredPhysicalCopyLaw Q (r₀*R) y) ≤
          ENNReal.ofReal (B*R^(-(d : ℝ)/2)) := by
  obtain ⟨F, hF, hscalar⟩ := parabolicSemigroupKernelDecay_canonical_column_moments
    hdecay d hd (AKMUpperEllipticity L) 1 (one_lt_AKMUpperEllipticity hL)
      (by norm_num) (by norm_num)
  have hm0 : 0 < m := zero_lt_two.trans_le hm
  have hn : 1+(d : ℝ)/2 < ((d+2 : ℕ) : ℝ) := by
    push_cast
    linarith [Nat.cast_nonneg (α := ℝ) d]
  obtain ⟨B, hB, hbound⟩ := recenteredPhysicalCopy_doubleBall_integrated_gradient_decay
    d (d+2) hd hn L r₀ (F m) (hF m hm0).le
  refine ⟨B, hB, ?_⟩
  intro Q i u G hum hGm hflow R hR y
  exact hbound Q i u G hum hGm hflow m hm
    (fun t ht x => (hscalar (actualCoefficientLaw Q)
      (isAdmissibleLaw_actualCoefficientLaw Q) i u G hum hflow m hm0 t ht x).2)
    R hR y

end EinsteinRelation.Correctors
