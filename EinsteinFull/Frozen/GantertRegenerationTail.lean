import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.RegenerationNoReturn
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External

open EinsteinRelation

/-- GMP Lemma 5.8, (5.22), and the no-return bound (5.20), for the
Section 7 zero-potential diffusion with the actual split coupling.
Literature assumption restricted to the literal cited tail and no-return facts.
No factorization, multi-cycle moment or lattice-renewal conclusion is assumed. -/
axiom gantert_regeneration_tail (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ) :
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K →
      ENNReal.ofReal (1 / 2 : ℝ) ≤
        Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam)) ∧
      ∀ t : ℝ, 0 ≤ t →
        Regeneration.annealedCoupledLaw Q.measure K
          {ωz | ENNReal.ofReal t < regenerationTime hd lam l 1 ωz.2} ≤
            ENNReal.ofReal (C * Real.exp (-c * lam ^ 2 * t))

end EinsteinFull.External
