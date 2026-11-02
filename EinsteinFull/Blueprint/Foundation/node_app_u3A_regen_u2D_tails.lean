import EinsteinFull.Frozen.GantertRegenerationTail
import EinsteinFull.Work.W5.UniformLatticeRenewalProof

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `app:regen-tails`, `paper/main.tex:1455–1462`.
At the fixed admissible GMP construction scale, the actual first cycle has
the cited tail and both exponential moments, including the infinite-time
branch. The construction scale threshold precedes the scale and coin
probability; all moment constants precede the law and force. This is not a
claim about arbitrary smaller scales or later cycles. -/
def node_app_u3A_regen_u2D_tailsStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C a M : ℝ, 0 < c ∧ 0 < C ∧ 0 < a ∧ a < c ∧ 0 < M ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    ∃ hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0,
      ENNReal.ofReal (1 / 2 : ℝ) ≤ Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ∧
      (∀ t : ℝ, 0 ≤ t → Regeneration.annealedCoupledLaw Q.measure K
        {ωz | ENNReal.ofReal t < regenerationTime hd lam l 1 ωz.2} ≤
          ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t))) ∧
      (∫⁻ ωz, Work.W5.regenerationExponentialWeight hd lam l a 1 ωz.2
        ∂Regeneration.annealedCoupledLaw Q.measure K) ≤ ENNReal.ofReal M ∧
      (∫⁻ ωz, Work.W5.regenerationExponentialWeight hd lam l a 1 ωz.2
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal M

end EinsteinFull.Blueprint
