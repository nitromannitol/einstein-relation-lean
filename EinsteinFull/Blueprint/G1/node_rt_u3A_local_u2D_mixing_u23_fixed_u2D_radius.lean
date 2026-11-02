import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.ReducedLaw
import EinsteinFull.Frozen.RegenerationTime
import Mathlib.MeasureTheory.Function.LpSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `rt:local-mixing#fixed-radius`, `paper/main.tex:425–451`.
The actual fixed-radius observations give both renewal equations. Each phase
has its own absolutely convergent limit series. The universal scalar
renewal clause uses the actual cycle law and retains arbitrary multiplicative
remainder bounds, so it also applies to the later exp(Cm) prefactor. Centering cancels that phase
in the second equation, including the omitted infinite q tail. Constants
precede the law, force, observations, phase and lattice index. -/
def node_rt_u3A_local_u2D_mixing_u23_fixed_u2D_radiusStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∀ b : ℝ, 0 < b →
    ∃ p c C : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    (let Δ := Regeneration.Renewal.regenDelta lam
     let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
     let mean := ∑' n : ℕ, (n : ℝ) * pn n
     ∀ (s : ℝ≥0), s < Δ → ∀ (h r hF rF : ℕ → ℝ) (q : ℕ → ℝ)
       (R Rf Bq : ℝ), 0 ≤ R → 0 ≤ Rf → 0 ≤ Bq →
     (∀ j, h j = r j + ∑ n ∈ Finset.range (j + 1), pn n * h (j - n)) →
     (∀ j, hF j = rF j + ∑ n ∈ Finset.range (j + 1), q n * h (j - n)) →
     (∀ j, |r j| ≤ R * Real.exp (-b * j)) →
     (∀ j, |rF j| ≤ Rf * Real.exp (-b * j)) →
     (∀ n, |q n| ≤ Bq * Real.exp (-b * n)) →
     Summable q → (∑' n, q n) = 0 →
     let H := mean⁻¹ * ∑' j : ℕ, r j
     Summable r ∧ |H| ≤ C * R ∧ ∀ j : ℕ,
       |h j - H| ≤ C * R * Real.exp (-c * j) ∧
       hF j = rF j +
         (∑ n ∈ Finset.range (j + 1), q n * (h (j - n) - H)) -
         H * ∑' n : ℕ, q (j + 1 + n) ∧
       |hF j| ≤ C * (Rf + Bq * R) * Real.exp (-c * j)) ∧
    (∀ F G : FieldPair d → ℝ,
    Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F →
    Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] G →
    MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
    MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
    (∫ ω, F ω ∂reducedLaw Q) = 0 →
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
    let Δ := Regeneration.Renewal.regenDelta lam
    let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
    let m := ∑' n : ℕ, (n : ℝ) * pn n
    let h := fun t : ℝ≥0 => ∫ ωz, G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let r := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l 1 ωz.2}, G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
    let hF := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
      G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let rF := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
      regenerationTime hd lam l 1 ωz.2}, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
    let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l 1 ωz.2 =
      (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
    let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
    let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
    let H := fun s : ℝ≥0 => m⁻¹ * ∑' j : ℕ, r (s + j * Δ)
    Summable q ∧ (∑' n, q n) = 0 ∧
    (∀ n : ℕ, |q n| ≤ C * Real.exp (-c * n) *
      (eLpNorm F 2 (reducedLaw Q)).toReal) ∧
    (∀ t : ℝ≥0, |r t| ≤ C * Real.exp (-c * lam ^ 2 * (t : ℝ)) * Ng ∧
      |rF t| ≤ C * Real.exp (-c * lam ^ 2 * (t : ℝ)) * Nf * Ng) ∧
    ∀ s : ℝ≥0, s < Δ →
      Summable (fun j : ℕ => r (s + j * Δ)) ∧ |H s| ≤ C * Ng ∧
      ∀ k : ℕ,
        h (s + k * Δ) = r (s + k * Δ) +
          ∑ n ∈ Finset.range (k + 1), pn n * h (s + (k - n) * Δ) ∧
        hF (s + k * Δ) = rF (s + k * Δ) +
          ∑ n ∈ Finset.range (k + 1), q n * h (s + (k - n) * Δ) ∧
        |h (s + k * Δ) - H s| ≤ C * Real.exp (-c * k) * Ng ∧
        hF (s + k * Δ) = rF (s + k * Δ) +
          (∑ n ∈ Finset.range (k + 1), q n * (h (s + (k - n) * Δ) - H s)) -
          H s * ∑' n : ℕ, q (k + 1 + n) ∧
        |hF (s + k * Δ)| ≤ C * Real.exp (-c * k) * Nf * Ng)

end EinsteinFull.Blueprint
