import EinsteinRelation.Calculus.HorizontalTranslationLp
import Mathlib.Analysis.Complex.Basic

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The actual complex `L²` translation action from Section 2, on the canonical
joint coefficient-pair space with its stationary law. -/
noncomputable def complexTranslation {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (x : Vec d) : Lp ℂ 2 Q →ₗᵢ[ℂ] Lp ℂ 2 Q :=
  Lp.compMeasurePreservingₗᵢ ℂ (translate x) (measurePreserving_translate Q hQ x)

end EinsteinFull
