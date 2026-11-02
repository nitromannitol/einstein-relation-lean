import EinsteinFull.Frozen.RegenerationLatticeMass
import EinsteinFull.Frozen.RegenerationRecord
import EinsteinRelation.Regeneration.ForcedBitSlice

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `rt:m-renewal`, `paper/main.tex:494–508`.
The actual terminal observable after m cycles is a measurable function of the
recorded future on D, and its conditional expectation satisfies the exact
lattice renewal identity. The cycle count is fixed before t; conditional
probabilities are the literal frozen lattice masses, with no renewal premise. -/
def node_rt_u3A_m_u2D_renewalStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ l δ : ℝ)
    (_hl : 0 < l) (_hsep : r₀ < 2 * l) (_hδ₀ : 0 < δ) (_hδ₁ : δ < 1),
  ∃ C : ℝ, 0 < C ∧
  ∀ (Q : EnvironmentLaw d Λ₀ r₀) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
  let Δ := Regeneration.Renewal.regenDelta lam
  let R := l / lam
  let i := Regeneration.Renewal.forceCoord hd
  ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd R) ≠ 0,
  let ν := regenerationConditionedLaw hd Q lam l K hK.1 hD
  ∀ A : ℝ, l ≤ A →
    let m := max 1 ⌈(A / l - 1) / 10⌉₊
    (m : ℝ) ≤ C * (1 + A) ∧
    ∀ G : FieldPair d → ℝ,
      Measurable[localSigma {x : Vec d | euclideanNorm x < A / lam}] G →
      Regeneration.BoundedRealTest G →
    let obs := fun (t : ℝ≥0) (ωz : FieldPair d × Regeneration.CoupledSample d) =>
      G (translate (ωz.2.1 t) (reduce ωz.1))
    let h := fun t : ℝ≥0 => ∫ ωz in
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)}, obs t ωz ∂ν
    let r := fun t : ℝ≥0 => ∫ ωz in
      {ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) ∧
        (t : ℝ≥0∞) < regenerationTime hd lam l (m + 1) ωz.2}, obs t ωz ∂ν
    ∀ t : ℝ≥0,
      (∃ Φ : Regeneration.FutureState d i R → ℝ,
        Measurable Φ ∧ Regeneration.BoundedRealTest Φ ∧
        (fun ωz => ({ωz | regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞)}.indicator
          (obs t)) ωz) =ᵐ[ν] (fun ωz => Φ (regenerationRecord hd lam l 0 ωz))) ∧
      (∀ᵐ ωz ∂ν, regenerationTime hd lam l m ωz.2 ≤ (t : ℝ≥0∞) →
        ∀ x : Vec d, euclideanNorm (x - ωz.2.1 t) < A / lam → -2 * R ≤ x i) ∧
      h t = r t + ∑ n ∈ Finset.range (⌊(t : ℝ) / (Δ : ℝ)⌋₊ + 1),
        regenerationLatticeMass hd Q lam l K hK.1 hD n * h (t - (n : ℝ≥0) * Δ)
end EinsteinFull.Blueprint
