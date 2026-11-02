import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.LatticeConvolutionPower
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint

open EinsteinRelation

/-- Exact statement mirror of `rt:renewal`; frozen declaration
`EinsteinFull.Frozen.uniform_lattice_renewal`, source `paper/main.tex:343–353`.
No anchor import or conclusion-bearing premise is used. -/
def node_rt_u3A_renewalStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C a M : ℝ, 0 < c ∧ 0 < C ∧ 0 < a ∧ 0 < M ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K,
    ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0,
      let p := regenerationLatticeMass hd Q lam l K hK.1 hD
      let m := ∑' n : ℕ, p n * (n : ℝ)
      (∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower p j n) - m⁻¹| ≤
        C * Real.exp (-c * n)) ∧
      (∀ j : ℕ,
        (∫⁻ ωz, if regenerationTime hd lam l j ωz.2 = ⊤ then ⊤ else
          ENNReal.ofReal (Real.exp (a * lam ^ 2 *
            (regenerationTime hd lam l j ωz.2).toReal))
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal (M ^ j)) ∧
      (∀ j : ℕ,
        (∫⁻ ωz, if regenerationTime hd lam l j ωz.2 = ⊤ then ⊤ else
          ENNReal.ofReal (Real.exp (a * lam ^ 2 *
            (regenerationTime hd lam l j ωz.2).toReal))
          ∂Regeneration.annealedCoupledLaw Q.measure K) ≤
            ENNReal.ofReal (C * M ^ j))

end EinsteinFull.Blueprint
