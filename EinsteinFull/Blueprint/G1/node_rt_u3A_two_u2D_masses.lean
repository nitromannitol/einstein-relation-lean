import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.LatticeConvolutionPower
import EinsteinFull.Work.W5.UniformLatticeRenewalProof
import EinsteinFull.Work.W5.RenewalNearOneSupport

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation
open EinsteinFull.Work.W5

/-- Graph node `rt:two-masses`, `paper/main.tex:377–377`.
The two atom bounds concern the actual conditional first-cycle lattice law.
The threshold and positive atom lower bound precede every law and force. -/
def node_rt_u3A_two_u2D_massesStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ ε : ℝ, 0 < ε ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    let p := regenerationLatticeMass hd Q lam l K hK.1 hD
    ε ≤ p 2 ∧ ε ≤ p 3

end EinsteinFull.Blueprint
