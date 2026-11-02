import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.RegenerationNoReturn
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `rt:renewal#coupling-parameter-transfer`,
`paper/main.tex:344–356`, with the probability tails at `1455–1462` and
the tube inputs at `356–377`. Each admissible scale and coin probability
precedes all probability constants, which precede the law, force and actual
split coupling. The tube events use the rescaled actual path and the literal
Euclidean distance. The successful coin is at the deterministic end of the
prebridge tube; no future no-return factorization or two-mass conclusion is
included. Exponential moments and cycle multiplication are separate nodes. -/
def node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transferStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ cD c C η : ℝ, ∃ N : ℕ,
      0 < cD ∧ 0 < c ∧ 0 < C ∧ 0 < η ∧ η ≤ 1 ∧ 0 < N ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K →
      let γ₂ : ℝ → Vec d := fun u =>
        min ((25 * l / 4) * u) (25 * l / 8) •
          unitVector (Regeneration.Renewal.forceCoord hd)
      let γ₃ : ℝ → Vec d := fun u => if u ≤ 1 then 0 else γ₂ (u - 1)
      let E : ℕ → Set (Path d) := fun j =>
        {Y | ∀ u : ℝ≥0, (u : ℝ) ≤ (j : ℝ) - 1 →
          euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal -
            (if j = 2 then γ₂ (u : ℝ) else γ₃ (u : ℝ))) < l / 32}
      ENNReal.ofReal cD ≤ Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ∧
      (∀ t : ℝ, 0 ≤ t → Regeneration.annealedCoupledLaw Q.measure K
        {ωz | ENNReal.ofReal t < regenerationTime hd lam l 1 ωz.2} ≤
          ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t))) ∧
      (∀ᵐ ω ∂Q.measure, ∀ j : ℕ, j = 2 ∨ j = 3 →
        ENNReal.ofReal (η ^ N) ≤ P (0, ω) (E j) ∧
        ENNReal.ofReal (δ * η ^ N) ≤ K (0, ω)
          {z | z.1 ∈ E j ∧ z.2 (j - 1) = true})

end EinsteinFull.Blueprint
