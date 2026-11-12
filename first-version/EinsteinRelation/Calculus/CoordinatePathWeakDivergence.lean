import EinsteinRelation.Calculus.PointwiseTranslationPrimitive
import EinsteinRelation.Calculus.CoordinatePathEndpoints
import EinsteinRelation.Calculus.WeakHorizontalFiniteSums

/-! # Full weak divergence of the literal coordinate path flux

Source: `paper/main.tex:1021–1029`. The segment primitives and the finite
endpoint cancellation give a concrete primitive of the translation difference.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation

/-- The actual coordinate path flux has the full endpoint source
(`paper/main.tex:1021–1029`). -/
theorem hasWeakHorizontalDivergence_coordinatePathFlux
    {d : ℕ} {Q : Measure (FieldPair d)} [IsProbabilityMeasure Q]
    (hQ : IsStationary Q) {f : FieldPair d → ℝ}
    (hf : Measurable f) (hf2 : MemLp f 2 Q) (z : Vec d) :
    HasWeakHorizontalDivergence Q hQ (coordinatePathFlux f z)
      (fun ω => f (translate z ω) - f ω) := by
  classical
  have hs (i : Fin d) : HasWeakHorizontalDivergence Q hQ
      (fun ω => Pi.single i (coordinatePathFlux f z ω i))
      (fun ω => f (translate (coordinateSegment z i (z i)) ω) -
        f (translate (coordinateSegment z i 0) ω)) := by
    have h := hasWeakHorizontalDivergence_literal_translationPrimitive hQ i (z i)
      (hf.comp (Probability.measurable_translate (coordinatePrefix z i.val)))
      (hf2.comp_measurePreserving (measurePreserving_translate Q hQ (coordinatePrefix z i.val)))
    simpa only [Function.comp_apply, translate_add, coordinateSegment,
      coordinatePathFlux, zero_smul, add_zero] using h
  have h := HasWeakHorizontalDivergence.finset_sum Finset.univ (fun i _ => hs i)
  convert h using 1
  · funext ω k
    simp [Finset.sum_apply, Pi.single_apply]
  · funext ω
    exact (sum_coordinatePath_endpoints z f ω).symm

end EinsteinRelation
