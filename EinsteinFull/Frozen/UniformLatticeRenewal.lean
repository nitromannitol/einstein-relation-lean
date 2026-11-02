import EinsteinFull.Proofs.UniformLatticeRenewal
import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.LatticeConvolutionPower
import EinsteinFull.Frozen.SmoothEnvironment
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Frozen

open EinsteinRelation

/-- Lemma 3.2 (`rt:renewal`), under Assumptions 1.1 and 1.2. -/
theorem uniform_lattice_renewal :
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) (hΛ : 1 ≤ Λ₀) (hr : 1 ≤ r₀),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C a M : ℝ, 0 < c ∧ 0 < C ∧ 0 < a ∧ 0 < M ∧
    ∀ (β : ℕ → ℝ) (hβ : ∀ k, 1 ≤ k → 0 < β k),
    let D : StructuralData d := ⟨Λ₀, r₀, β, hΛ, hr, hβ⟩
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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
          ∂ Regeneration.annealedCoupledLaw Q.measure K) ≤
            ENNReal.ofReal (C * M ^ j)) := by
  exact EinsteinFull.Proofs.uniform_lattice_renewal

end EinsteinFull.Frozen
