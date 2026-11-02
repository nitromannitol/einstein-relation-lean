import EinsteinFull.Frozen.RegenerationConditionedLaw
import EinsteinFull.Frozen.ReducedLaw
import EinsteinFull.Frozen.RegenerationCoupling
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `rt:remainder-moment`, `paper/main.tex:398–413`.
Deterministic-time remainder estimate on the actual split path law, also
conditioned on D. The event bound is under the unconditioned law. The fixed
lower bound on D is supplied by the regeneration-tail input at l >= l₀. The
finite exponent precedes the observables, event, time and environment law;
J affects only the prefactor. Observations are of the reduced joint fields. -/
def node_rt_u3A_remainder_u2D_momentStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (B b : ℝ), 0 < B → 0 < b →
    ∃ l₀ p c C : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧ 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (l δ : ℝ), l₀ ≤ l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ F G : FieldPair d → ℝ,
    Measurable F → Measurable G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    ∀ (J : ℝ) (t : ℝ≥0) (A : Set (FieldPair d × Regeneration.CoupledSample d)),
    0 ≤ J → MeasurableSet A →
    Regeneration.annealedCoupledLaw Q.measure K A ≤
      ENNReal.ofReal (B * Real.exp (B * J - b * lam ^ 2 * (t : ℝ))) →
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      IntegrableOn (fun ωz => F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1))) A μ ∧
      |∫ ωz in A, F (reduce ωz.1) * G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ| ≤
        C * Real.exp (C * J - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal

end EinsteinFull.Blueprint
