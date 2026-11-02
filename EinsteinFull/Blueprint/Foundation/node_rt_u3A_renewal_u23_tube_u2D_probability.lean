import EinsteinFull.Frozen.RegenerationCoupling
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `rt:renewal#tube-probability`, `paper/main.tex:370–375`,
with the prescribed tubes at `356–368`. The fixed subdivision, containing
ball, weighted ellipticity bounds and probability constants precede the law
and force. The killed endpoint lower bound is stated as domination of
Lebesgue measure by the actual rescaled path law, uniformly over starting
points in each small ball. Reversibility and domain monotonicity are proof
steps for this conclusion, not premises or replacement kernel objects.
One environment event supplies both tubes and every starting point. -/
def node_rt_u3A_renewal_u23_tube_u2D_probabilityStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l : ℝ), 0 < l →
    let i := Regeneration.Renewal.forceCoord hd
    let ε := l / 32
    let γ₂ : ℝ → Vec d := fun u =>
      min ((25 * l / 4) * u) (25 * l / 8) • unitVector i
    let γ₃ : ℝ → Vec d := fun u => if u ≤ 1 then 0 else γ₂ (u - 1)
    let γ : ℕ → ℝ → Vec d := fun j => if j = 2 then γ₂ else γ₃
    ∃ B C cstar η : ℝ, ∃ N : ℕ,
      0 < B ∧ 1 ≤ C ∧ 0 < cstar ∧ 0 < η ∧ η ≤ 1 ∧ 0 < N ∧
      (∀ j : ℕ, j = 2 ∨ j = 3 →
        let h : ℝ := ((j : ℝ) - 1) / N
        0 < h ∧ (N : ℝ) * h = (j : ℝ) - 1 ∧
        (∀ u : ℝ, 0 ≤ u → u ≤ (j : ℝ) - 1 →
          euclideanNorm (γ j u) + ε < B) ∧
        (∀ k : ℕ, k < N → ∀ u : ℝ,
          (k : ℝ) * h ≤ u → u ≤ (k + 1 : ℕ) * h →
          euclideanNorm (γ j u - γ j ((k : ℝ) * h)) ≤ ε / 16)) ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d),
    IsGMPReducedKernel hd Q.ellipticity_parameter Q lam h₀.le h₁ P →
      ∀ᵐ ω ∂Q.measure,
        let ρ : Vec d → ℝ := fun x => Real.exp (2 * x i)
        let α : Vec d → Mat d := fun x =>
          (ρ x / 2) • reducedCoefficient ω (lam⁻¹ • x)
        (∀ x : Vec d, euclideanNorm x < B →
          C⁻¹ ≤ ρ x ∧ ρ x ≤ C ∧ (α x).transpose = α x ∧
          ∀ v : Vec d,
            C⁻¹ * euclideanSq v ≤ dot v ((α x).mulVec v) ∧
            dot v ((α x).mulVec v) ≤ C * euclideanSq v) ∧
        ∀ j : ℕ, j = 2 ∨ j = 3 →
          let h : ℝ := ((j : ℝ) - 1) / N
          let c : ℕ → Vec d := fun k => γ j ((k : ℝ) * h)
          let piece : ℕ → Set (Path d) := fun k =>
            {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
                euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - c k) < ε / 2) ∧
              euclideanNorm (lam • Y (h / lam ^ 2).toNNReal - c (k + 1)) < ε / 16}
          (∀ k : ℕ, k < N → ∀ x : Vec d,
            euclideanNorm (x - c k) < ε / 16 →
              (∀ A : Set (Vec d), MeasurableSet A →
                A ⊆ {y | euclideanNorm (y - c (k + 1)) < ε / 16} →
                ENNReal.ofReal cstar * volume A ≤ P (lam⁻¹ • x, ω)
                  {Y | (∀ u : ℝ≥0, (u : ℝ) ≤ h →
                      euclideanNorm
                        (lam • Y ((u : ℝ) / lam ^ 2).toNNReal - c k) < ε / 2) ∧
                    lam • Y (h / lam ^ 2).toNNReal ∈ A}) ∧
              ENNReal.ofReal η ≤ P (lam⁻¹ • x, ω) (piece k)) ∧
          ENNReal.ofReal (η ^ N) ≤ P (0, ω)
            {Y | ∀ u : ℝ≥0, (u : ℝ) ≤ (j : ℝ) - 1 →
              euclideanNorm (lam • Y ((u : ℝ) / lam ^ 2).toNNReal -
                γ j (u : ℝ)) < ε}

end EinsteinFull.Blueprint
