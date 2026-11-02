import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.LatticeConvolutionPower
import EinsteinFull.Work.W5.UniformLatticeRenewalProof
import EinsteinFull.Work.W5.RenewalNearOneSupport

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation
open EinsteinFull.Work.W5

/-- Graph node `rt:many-cycle-moment`, `paper/main.tex:393–393`.
Moment multiplication for the actual successive regeneration times.
The conditioned law has no first-cycle prefactor, while the original law
retains one. Infinite regeneration times have infinite exponential weight. -/
def node_rt_u3A_many_u2D_cycle_u2D_momentStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a M C : ℝ, 0 < a ∧ 0 < M ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    (∀ j : ℕ,
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a j ωz.2
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal (M ^ j)) ∧
    (∀ j : ℕ,
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a j ωz.2
        ∂Regeneration.annealedCoupledLaw Q.measure K) ≤ ENNReal.ofReal (C * M ^ j))

end EinsteinFull.Blueprint
