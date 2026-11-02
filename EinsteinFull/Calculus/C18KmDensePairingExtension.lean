import EinsteinFull.Blueprint.G1.Proofs.SbxS4KmPathIdentification
import EinsteinFull.Calculus.ComplexHighExponentSupport
import EinsteinFull.Calculus.ComplexForceSemigroupSupport

/-! Extension of the canonical action from bounded continuous tests. -/

open MeasureTheory
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- A bounded-test identification extends to any reduced-law L² observable
with a finite higher moment. -/
theorem c18_km_extend_canonical_action_from_bounded
    {d : ℕ} (hd : 2 ≤ d) {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (q : ℝ≥0∞) (hq : 2 ≤ q) (hqfin : q ≠ ∞)
    (lam : ℝ) (t : ℝ≥0) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
    ∀ (T : Lp ℂ q (reducedLaw Q) →L[ℂ] Lp ℂ 2 Q.measure)
    (_hbounded : ∀ f : BoundedContinuousFunction (FieldPair d) ℂ,
      T (BoundedContinuousFunction.toLp q (reducedLaw Q) ℂ f) =ᵐ[Q.measure]
        fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) t
          (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f) (reduce ω))
    (G : Lp ℂ 2 (reducedLaw Q)) (hGq : MemLp (G : FieldPair d → ℂ) q (reducedLaw Q)),
    T (hGq.toLp (G : FieldPair d → ℂ)) =ᵐ[Q.measure]
      fun ω => forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) t G (reduce ω) := by
  let _ : IsProbabilityMeasure (reducedLaw Q) := reducedLaw_probability Q
  let _ : Fact (1 ≤ q) := ⟨le_trans (by norm_num) hq⟩
  intro T hbounded G hGq
  let _ : PolishSpace (CoefficientField d) := Localization.coefficientField_polish d
  let _ : PolishSpace (FieldPair d) := inferInstance
  let P := (sbxS4ReducedPullback Q).toContinuousLinearMap
  let I := complexLpToL2CLM (reducedLaw Q) hq
  let A := forcedComplexEvolution Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) t
  have hpull : ∀ F : Lp ℂ 2 (reducedLaw Q), P F =ᵐ[Q.measure] fun ω => F (reduce ω) := by
    intro F
    exact Lp.coeFn_compMeasurePreserving F ⟨Probability.measurable_reduce, rfl⟩
  have hmaps : T = P.comp (A.comp I) := by
    apply ContinuousLinearMap.ext
    intro u
    refine (BoundedContinuousFunction.toLp_denseRange ℂ (reducedLaw Q) ℂ hqfin).induction_on u
      (isClosed_eq T.continuous (P.comp (A.comp I)).continuous) ?_
    intro f
    have hincl : I (BoundedContinuousFunction.toLp q (reducedLaw Q) ℂ f) =
        BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f := by
      apply Lp.ext
      exact (BoundedContinuousFunction.coeFn_toLp q (reducedLaw Q) ℂ f).trans
        (BoundedContinuousFunction.coeFn_toLp 2 (reducedLaw Q) ℂ f).symm
    apply Lp.ext
    refine (hbounded f).trans ?_
    simpa only [ContinuousLinearMap.comp_apply, hincl] using
      (hpull (A (BoundedContinuousFunction.toLp 2 (reducedLaw Q) ℂ f))).symm
  have hG : I (hGq.toLp (G : FieldPair d → ℂ)) = G := by
    apply Lp.ext
    exact hGq.coeFn_toLp
  rw [hmaps]
  simpa only [ContinuousLinearMap.comp_apply, hG] using hpull (A G)

end EinsteinFull.Blueprint
