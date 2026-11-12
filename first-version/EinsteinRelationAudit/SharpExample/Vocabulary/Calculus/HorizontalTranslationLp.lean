import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Function.LpSpace.ContinuousCompMeasurePreserving
import Mathlib.MeasureTheory.Measure.RegularityCompacts
import Mathlib.Topology.ContinuousMap.SecondCountableSpace
import Mathlib.Topology.Metrizable.ContinuousMap
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.CoefficientRestriction
import EinsteinRelationAudit.SharpExample.Vocabulary.Probability.LocalSigma

/-! Restated from the library module `EinsteinRelation.Calculus.HorizontalTranslationLp`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory
noncomputable section
namespace EinsteinRelation
theorem measurePreserving_translate {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) : MeasurePreserving (translate x) Q Q :=
  ⟨Probability.measurable_translate x, hQ x⟩
def translationLp {d : ℕ} (Q : Measure (FieldPair d)) (hQ : IsStationary Q)
    (x : Vec d) : Lp ℝ 2 Q →ₗᵢ[ℝ] Lp ℝ 2 Q :=
  Lp.compMeasurePreservingₗᵢ ℝ (translate x) (measurePreserving_translate Q hQ x)
end EinsteinRelation
