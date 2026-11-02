import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.LatticeConvolutionPower
import EinsteinFull.Work.W5.UniformLatticeRenewalProof
import EinsteinFull.Work.W5.RenewalNearOneSupport

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation
open EinsteinFull.Work.W5

/-- Graph node `rt:renewal#cauchy`, `paper/main.tex:386–391`.
The actual removable renewal resolvent is uniformly holomorphic and bounded
on a fixed larger disc. Its Taylor coefficients are the literal renewal
coefficients, giving the exponential lattice estimate for every index. -/
def node_rt_u3A_renewal_u23_cauchyStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ ρ B c C : ℝ, 0 < ρ ∧ 0 < B ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    let p := regenerationLatticeMass hd Q lam l K hK.1 hD
    let V := renewalRemovableDifference p
    AnalyticOnNhd ℂ V (Metric.closedBall 0 (1 + ρ)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → ‖V z‖ ≤ B) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → z ≠ 1 →
      V z = (1 - renewalGenerating p z)⁻¹ -
        ((renewalMean p : ℂ) * (1 - z))⁻¹) ∧
    (∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower p j n) -
      (renewalMean p)⁻¹| ≤ C * Real.exp (-c * n))

end EinsteinFull.Blueprint
