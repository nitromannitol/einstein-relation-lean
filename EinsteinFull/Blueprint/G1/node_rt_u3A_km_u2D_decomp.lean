import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.RegenerationTime
import EinsteinFull.Frozen.RealLocalObservation
import EinsteinFull.Frozen.ComplexEnvironmentSemigroup
import Mathlib.Analysis.SpecialFunctions.Exp

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `rt:km-decomp`, `paper/main.tex:520–534`.
The literal k/m-cycle decomposition, summable centered coefficients and phase
cancellation for positive force, followed by the actual semigroup covariance
estimate for both force signs. The prescribed k,m depend on A/l only. All
constants precede A and the law; the decay rate has no radius dependence.
The negative-force conclusion makes no reflection-invariance assumption. -/
def node_rt_u3A_km_u2D_decompStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ),
    ∃ l₀ : ℝ, 0 < l₀ ∧ r₀ < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ p c C lam₀ : ℝ, 2 ≤ p ∧ 0 < c ∧ 0 < C ∧ 0 < lam₀ ∧ lam₀ ≤ 1 ∧
    ∀ Q : EnvironmentLaw d Λ₀ r₀,
    (∀ (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1), lam ≤ lam₀ →
      ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
        (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
        (hD : Regeneration.annealedCoupledLaw Q.measure K
          (regenerationNoReturn hd (l / lam)) ≠ 0),
      ∀ A : ℝ, l ≤ A → ∀ F G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] F →
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
      MemLp F (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp G (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 →
      let k : ℕ := max 1 ⌈(A / l + 4) / 10⌉₊
      let m : ℕ := max 1 ⌈(A / l - 1) / 10⌉₊
      let μ := Regeneration.annealedCoupledLaw Q.measure K
      let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
      let Δ := Regeneration.Renewal.regenDelta lam
      let pn := regenerationLatticeMass hd Q lam l K hK.1 hD
      let mean := ∑' n : ℕ, (n : ℝ) * pn n
      let q := fun n : ℕ => ∫ ωz in {ωz | regenerationTime hd lam l k ωz.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F (reduce ωz.1) ∂μ
      let hm := fun t : ℝ≥0 => ∫ ωz in {ωz |
        regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)},
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
      let rm := fun t : ℝ≥0 => ∫ ωz in {ωz |
        regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2},
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂ν
      let Hm := fun s : ℝ≥0 => mean⁻¹ * ∑' j : ℕ, rm (s + j * Δ)
      let cov := fun t : ℝ≥0 => ∫ ωz, F (reduce ωz.1) *
        G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
      let rem := fun t : ℝ≥0 => ∫ ωz in {ωz | (t : ℝ≥0∞) <
        regenerationTime hd lam l (k + m) ωz.2}, F (reduce ωz.1) *
          G (translate (ωz.2.1 t) (reduce ωz.1)) ∂μ
      let Nf := (eLpNorm F (ENNReal.ofReal p) (reducedLaw Q)).toReal
      let Ng := (eLpNorm G (ENNReal.ofReal p) (reducedLaw Q)).toReal
      (k + m : ℝ) ≤ C * (1 + A) ∧
      Summable q ∧ (∑' n, q n) = 0 ∧
      (∀ n : ℕ, |q n| ≤ C * Real.exp (C * k - c * n) * Nf) ∧
      (∀ t : ℝ≥0,
        Integrable (fun ωz => F (reduce ωz.1) *
          G (translate (ωz.2.1 t) (reduce ωz.1))) μ ∧
        cov t = rem t + ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
          q n * hm (t - n * Δ) ∧
        |rem t| ≤ C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng ∧
        |cov t| ≤ C * Real.exp (C * (k + m) - c * lam ^ 2 * (t : ℝ)) * Nf * Ng) ∧
      ∀ s : ℝ≥0, s < Δ → ∀ j : ℕ,
        cov (s + j * Δ) = rem (s + j * Δ) +
          (∑ n ∈ Finset.range (j + 1), q n * (hm (s + (j - n) * Δ) - Hm s)) -
          Hm s * ∑' n : ℕ, q (j + 1 + n)) ∧
    (∀ lam : ℝ, 0 < |lam| → |lam| ≤ lam₀ →
      ∀ S : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      IsComplexEnvironmentSemigroup Q (Regeneration.Renewal.forceCoord hd) (lam : ℂ) S →
      ∀ A : ℝ, l ≤ A → ∀ F G : Lp ℂ 2 (reducedLaw Q),
      IsRealLocalObservation Q (A / |lam|) F →
      IsRealLocalObservation Q (A / |lam|) G →
      MemLp (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      MemLp (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q) →
      (∫ ω, F ω ∂reducedLaw Q) = 0 → ∀ t : ℝ≥0,
      ‖∫ ω, F ω * S t G ω ∂reducedLaw Q‖ ≤
        C * Real.exp (C * A - c * lam ^ 2 * (t : ℝ)) *
          (eLpNorm (F : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal *
          (eLpNorm (G : FieldPair d → ℂ) (ENNReal.ofReal p) (reducedLaw Q)).toReal)

end EinsteinFull.Blueprint
