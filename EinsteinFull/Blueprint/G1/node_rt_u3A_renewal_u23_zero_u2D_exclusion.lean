import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.LatticeConvolutionPower
import EinsteinFull.Work.W5.UniformLatticeRenewalProof
import EinsteinFull.Work.W5.RenewalNearOneSupport

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation
open EinsteinFull.Work.W5

/-- Graph node `rt:renewal#zero-exclusion`, `paper/main.tex:379–384`.
The actual probability generating function, its derivatives and its removable
divided difference have uniform bounds on a larger disc. The near-one bound
and the annular deficit bound precede the law. These bounds, rather than
pointwise nonvanishing alone, are the data used by the Cauchy argument. -/
def node_rt_u3A_renewal_u23_zero_u2D_exclusionStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ ρ h κ B : ℝ, 0 < ρ ∧ 0 < h ∧ 0 < κ ∧ 0 < B ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    let p := regenerationLatticeMass hd Q lam l K hK.1 hD
    let f := renewalGenerating p
    let g := renewalDividedDifference p
    let m := renewalMean p
    2 ≤ m ∧ m ≤ B ∧
    AnalyticOnNhd ℂ f (Metric.closedBall 0 (1 + 2 * ρ)) ∧
    AnalyticOnNhd ℂ g (Metric.closedBall 0 (1 + 2 * ρ)) ∧
    g 1 = (m : ℂ) ∧ HasDerivAt f (m : ℂ) 1 ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + 2 * ρ →
      ‖f z‖ + ‖deriv f z‖ + ‖iteratedDeriv 2 f z‖ ≤ B) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → 1 - f z = (1 - z) * g z) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → ‖z - 1‖ ≤ 2 * h → 1 ≤ ‖g z‖) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → 2 * h ≤ ‖z - 1‖ → κ ≤ ‖1 - f z‖) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → (1 - f z = 0 ↔ z = 1))

end EinsteinFull.Blueprint
