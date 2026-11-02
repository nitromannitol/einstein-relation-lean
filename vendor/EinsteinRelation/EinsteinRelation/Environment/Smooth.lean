import EinsteinRelation.Environment.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs

/-! Smoothness in Proposition 7.1 (`sharp.example`, `paper/main.tex:1202–1209`).
Matrix smoothness is stated entrywise on the existing coordinate carrier; the
ellipticity and Lipschitz bounds continue to use the explicit Euclidean norms.
-/

namespace EinsteinRelation

/-- The physical matrix entries and potential are smooth on all of space. -/
def IsSmoothFieldPair {d : ℕ} (ω : FieldPair d) : Prop :=
  (∀ j k, ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.1 x j k)) ∧
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ω.2 x)

end EinsteinRelation
