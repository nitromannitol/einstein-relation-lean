import Mathlib.MeasureTheory.Integral.Bochner.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Basic

/-! Restated from the library module `EinsteinRelation.Probability.LocalSigma`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

namespace EinsteinRelation.Probability
/-- Joint continuity for the compact-open topology on coefficient pairs. -/
theorem continuous_translate {d : ℕ} :
    Continuous (fun p : Vec d × FieldPair d => translate p.1 p.2) := by
  apply Continuous.prodMk
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_fst.snd.fst).eval (continuous_fst.fst.add continuous_snd)
  · apply ContinuousMap.continuous_of_continuous_uncurry
    exact (continuous_fst.snd.snd).eval (continuous_fst.fst.add continuous_snd)
/-- Fixed translations are measurable for the canonical coefficient law. -/
theorem measurable_translate {d : ℕ} (x : Vec d) : Measurable (translate x) :=
  (continuous_translate.comp (continuous_const.prodMk continuous_id)).measurable
end EinsteinRelation.Probability
