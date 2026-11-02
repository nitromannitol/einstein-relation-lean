import EinsteinFull.Frozen.RegenerationCoupling
import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.RegenerationRecord
import EinsteinFull.Frozen.RegenerationConditionedLaw
import EinsteinRelation.Regeneration.FirstRegenerationSliceFubini

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

set_option linter.unusedVariables false in
/-- Exact statement mirror of `rt:factorization`; frozen declaration
`EinsteinFull.Frozen.environmental_factorization`, source `paper/main.tex:329–337`.
No anchor import or conclusion-bearing premise is used. -/
def node_rt_u3A_factorizationStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : r₀ < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0),
    (∀ (F : FieldPair d → ℝ),
      Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F →
      Regeneration.BoundedRealTest F →
      ∀ (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ → ∀ n : ℕ,
      ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK.1 hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      (∫ ωz in {ωz | regenerationTime hd lam l 1 ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F ωz.1 * Φ (regenerationRecord hd lam l 1 ωz) ∂μ) =
      (∫ ωz in {ωz | regenerationTime hd lam l 1 ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F ωz.1 ∂μ) *
      ∫ ωz, Φ (regenerationRecord hd lam l 0 ωz)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ∧
    (∀ (m : ℕ) (H : Regeneration.CoupledSample d → ℝ),
      Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] H →
      Regeneration.BoundedRealTest H → ∀ y : Vec d,
      ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d |
          x (Regeneration.Renewal.forceCoord hd) ≤
            y (Regeneration.Renewal.forceCoord hd) - 4 * (l / lam)}] A ∧
        (fun ω => Regeneration.firstSlicePastIntegral
          (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) m K H (y, ω)) =ᵐ[Q.measure] A)

end EinsteinFull.Blueprint
