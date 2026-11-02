import EinsteinFull.Frozen.LatticeConvolutionPower
import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.ReducedLaw
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `rt:local-mixing#phase-error`, `paper/main.tex:508–518`.
The actual terminal m-cycle functional has a phase-dependent renewal limit.
The support condition is precisely the recorded-future half-space condition.
The sole m dependence in the bounds is the displayed exponential prefactor;
there is no assertion that the limit is independent of phase. -/
def node_rt_u3A_local_u2D_mixing_u23_phase_u2D_errorStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ (A : ℝ) (m : ℕ), l ≤ A → 1 ≤ m → 10 * (m : ℝ) * l - l - A ≥ -2 * l →
    ∀ G : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let mean := ∑' n : ℕ, (n : ℝ) * pn n
    let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
      regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
      (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
    let Hm := fun s : ℝ≥0 => mean⁻¹ * ∑' j : ℕ, rm (s + j * Δ)
    (∀ t : ℝ≥0, |rm t| ≤ C * Real.exp (C * m - c * lam ^ 2 * (t : ℝ)) * Ng) ∧
    ∀ s : ℝ≥0, s < Δ →
      Summable (fun j : ℕ => rm (s + j * Δ)) ∧
      |Hm s| ≤ C * Real.exp (C * m) * Ng ∧
      ∀ j : ℕ,
        hm (s + j * Δ) = rm (s + j * Δ) +
          ∑ n ∈ Finset.range (j + 1), pn n * hm (s + (j - n) * Δ) ∧
        hm (s + j * Δ) - Hm s =
          (∑ n ∈ Finset.range (j + 1),
            ((∑' a : ℕ, EinsteinFull.latticeConvolutionPower pn a (j - n)) - mean⁻¹) *
              rm (s + n * Δ)) - mean⁻¹ * ∑' n : ℕ, rm (s + (j + 1 + n) * Δ) ∧
        |hm (s + j * Δ) - Hm s| ≤ C * Real.exp (C * m - c * j) * Ng

end EinsteinFull.Blueprint
