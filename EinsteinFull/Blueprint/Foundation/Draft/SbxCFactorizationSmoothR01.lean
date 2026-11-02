import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_independence_v2
import EinsteinFull.Blueprint.G1.node_app_u3A_factorization_u23_condition_u2D_iterate
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_coupling_u2D_scope
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_past_u2D_kernel
import EinsteinFull.Blueprint.Foundation.node_app_u3A_factorization_u23_slices
import EinsteinFull.Blueprint.Roots.node_app_u3A_factorization
import EinsteinFull.Blueprint.Roots.node_rt_u3A_factorization
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Blueprint.G1.node_rt_u3A_factorization_u23_small_u2D_indices

/-! Literal smooth-law variants of the factorization graph. Draft conditional contracts.
The positive auxiliary force covers (0,1]; the signed local-mixing application uses
direction -e₁, with no reflection invariance assumption. -/
open MeasureTheory
open scoped NNReal ENNReal
namespace EinsteinFull.Blueprint.SbxCFactorizationR01
open EinsteinRelation EinsteinFull.Blueprint

set_option linter.unusedVariables false in
def independenceSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → D.dependenceRange < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0,
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K
      hK.1 hD
    ∀ (Φ : Regeneration.FutureState d i R → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ →
    (∀ (F : FieldPair d → ℝ),
      Measurable[localSigma {x : Vec d | euclideanNorm x < R}] F →
      Regeneration.BoundedRealTest F →
    ∀ (n : ℕ), 2 ≤ n → ∀ (H : Regeneration.CoupledSample d → ℝ),
      Measurable[Regeneration.finiteHistorySigma Δ (n - 1)] H →
      Regeneration.BoundedRealTest H →
    let A := fun (y : Vec d) (ω : FieldPair d) =>
      F ω * Regeneration.firstSlicePastIntegral Δ lam R i (n - 1) K H (y, ω)
    let B := fun (y : Vec d) (ω : FieldPair d) =>
      ∫ z, Regeneration.killedFutureTest R i Φ ((y, ω), z) ∂K (y, ω)
    ((D.dependenceRange < 2 * R) ∧
      (∀ᵐ y ∂(volume : Measure (Vec d)), y i < 10 * R → A y =ᵐ[Q.measure] 0) ∧
      (∀ᵐ y ∂(volume : Measure (Vec d)), 10 * R ≤ y i →
        (∃ A' B' : FieldPair d → ℝ,
          Measurable[localSigma {x : Vec d | x i ≤ y i - 4 * R}] A' ∧
          Measurable[localSigma {x : Vec d | y i - 2 * R ≤ x i}] B' ∧
          A y =ᵐ[Q.measure] A' ∧ B y =ᵐ[Q.measure] B') ∧
        (∫ ω, A y ω * B y ω ∂Q.measure) =
          (∫ ω, A y ω ∂Q.measure) * ∫ ω, B y ω ∂Q.measure) ∧
      (∀ᵐ y ∂(volume : Measure (Vec d)), (∫ ω, B y ω ∂Q.measure) =
        ∫ q in regenerationNoReturn hd R, Φ (regenerationRecord hd lam l 0 q) ∂μ) ∧
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
        F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂μ) =
      (∫ q in {q | regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F q.1 * H q.2 ∂μ) *
        ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν)) ∧
    (∫ q, Φ (regenerationRecord hd lam l 1 q) ∂μ) =
      ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν


set_option linter.unusedVariables false in
def conditionIterateSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → D.dependenceRange < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    ∀ hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0,
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    let μ := Regeneration.annealedCoupledLaw Q.measure K
    let ν := regenerationConditionedLaw hd Q lam l K
      hK.1 hD
    (∀ n : ℕ, 2 ≤ n → ∀ᵐ q ∂μ,
      regenerationTime hd lam l 1 q.2 =
        (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) →
      (q ∈ regenerationNoReturn hd R ↔
        ∀ s : ℝ≥0, s ≤ (n - 1 : ℕ) * Δ → -R < q.2.1 s i)) ∧
    (∃ Θ : Regeneration.FutureState d i R → Regeneration.FutureState d i R,
      Measurable Θ ∧
      (∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        ∀ k : ℕ, ∀ᵐ q ∂ρ,
          Θ (regenerationRecord hd lam l k q) = regenerationRecord hd lam l (k + 1) q) ∧
      Measure.map Θ (Measure.map (regenerationRecord hd lam l 0) ν) =
        Measure.map (regenerationRecord hd lam l 0) ν) ∧
    (∀ (Φ : Regeneration.FutureState d i R → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ →
      ∀ ρ ∈ ({μ, ν} : Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      (∀ k : ℕ, 1 ≤ k →
        (∫ q, Φ (regenerationRecord hd lam l k q) ∂ρ) =
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν) ∧
      (∀ (F : FieldPair d → ℝ),
        Measurable[localSigma {x : Vec d | euclideanNorm x < R}] F →
        Regeneration.BoundedRealTest F →
        ∀ (n : ℕ), 2 ≤ n → ∀ (H : Regeneration.CoupledSample d → ℝ),
        Measurable[Regeneration.finiteHistorySigma Δ (n - 1)] H →
        Regeneration.BoundedRealTest H →
        (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)},
          F q.1 * H q.2 * Φ (regenerationRecord hd lam l 1 q) ∂ρ) =
        (∫ q in {q | regenerationTime hd lam l 1 q.2 =
          (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞)}, F q.1 * H q.2 ∂ρ) *
          ∫ q, Φ (regenerationRecord hd lam l 0 q) ∂ν))


set_option linter.unusedVariables false in
def couplingScopeSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → D.dependenceRange < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    let Δ := Regeneration.Renewal.regenDelta lam
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    ∀ k : ℕ,
      Measurable (regenerationTime hd lam l k) ∧
      Measurable (regenerationRecord hd lam l k) ∧
      ∀ ρ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK.1 hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
        ∀ᵐ q ∂ρ, ∃ n : ℕ, 2 * k ≤ n ∧
          regenerationTime hd lam l k q.2 =
            (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ∧
          regenerationRecord hd lam l k q =
            Regeneration.futureRecord Δ R q.1 q.2 i ((n : ℝ≥0) * Δ)


set_option linter.unusedVariables false in
def pastKernelSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → D.dependenceRange < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    ∀ (m : ℕ) (v : ℝ) (H : Regeneration.CoupledSample d → ℝ),
      Measurable[Regeneration.finiteHistorySigma Δ m] H →
      Regeneration.BoundedRealTest H →
      (∀ z, (¬ ∀ t : ℝ≥0, t ≤ (m : ℝ≥0) * Δ → z.1 t i ≤ v) → H z = 0) →
      ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d | x i ≤ v + 3 * R}] A ∧
        (fun ω => ∫ z, H z ∂K (0, ω)) =ᵐ[Q.measure] A


set_option linter.unusedVariables false in
def slicesSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ), 0 < l → D.dependenceRange < 2 * l → 0 < δ → δ < 1 →
    ∀ (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d),
    ∀ (_hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K),
    let R := l / lam
    let i := Regeneration.Renewal.forceCoord hd
    let Δ := Regeneration.Renewal.regenDelta lam
    ∀ (n : ℕ), 2 ≤ n →
    let T := ((n - 1 : ℕ) : ℝ≥0) * Δ
    let Γ := Regeneration.forcedBitTrialEvent Δ lam R i (n - 1)
    MeasurableSet[Regeneration.finiteHistorySigma Δ (n - 1)] Γ ∧
      (∀ z : Regeneration.CoupledSample d,
        regenerationTime hd lam l 1 z = (((n : ℝ≥0) * Δ : ℝ≥0) : ℝ≥0∞) ↔
          z ∈ Γ ∧ z.2 (n - 1) = true ∧
            Regeneration.NoBacktracking R
              (Regeneration.pathTimeShift z.1 ((n : ℝ≥0) * Δ)) i) ∧
      (∀ z : Regeneration.CoupledSample d, z.1 0 = 0 → z ∈ Γ →
        let a := z.1 T
        2 * R ≤ a i ∧
          (∀ t : ℝ≥0, t ≤ T → z.1 t i ≤ a i + R) ∧
          ∀ y : Vec d, y ∈ Regeneration.endpointBall i R a →
            10 * R ≤ y i ∧
              ∀ t : ℝ≥0, t ≤ T → z.1 t i ≤ y i - 7 * R)


set_option linter.unusedVariables false in
def appendixFactorizationSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : D.dependenceRange < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0),
    ∀ (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ),
    Measurable Φ → Regeneration.BoundedRealTest Φ →
    ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
      regenerationConditionedLaw hd Q lam l K hK.1 hD} :
        Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      (∀ k : ℕ, 1 ≤ k →
        (∫ ωz, Φ (regenerationRecord hd lam l k ωz) ∂μ) =
          ∫ ωz, Φ (regenerationRecord hd lam l 0 ωz)
            ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ∧
      (∀ (F : FieldPair d → ℝ),
        Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F →
        Regeneration.BoundedRealTest F →
        ∀ (n : ℕ), 2 ≤ n → ∀ H : Regeneration.CoupledSample d → ℝ,
        Measurable[Regeneration.finiteHistorySigma
          (Regeneration.Renewal.regenDelta lam) (n - 1)] H →
        Regeneration.BoundedRealTest H →
        (∫ ωz in {ωz | regenerationTime hd lam l 1 ωz.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
          F ωz.1 * H ωz.2 * Φ (regenerationRecord hd lam l 1 ωz) ∂μ) =
        (∫ ωz in {ωz | regenerationTime hd lam l 1 ωz.2 =
          (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
          F ωz.1 * H ωz.2 ∂μ) *
        ∫ ωz, Φ (regenerationRecord hd lam l 0 ωz)
          ∂regenerationConditionedLaw hd Q lam l K hK.1 hD)


set_option linter.unusedVariables false in
def environmentalFactorizationSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
    (l δ : ℝ) (hl : 0 < l) (hsep : D.dependenceRange < 2 * l) (hδ₀ : 0 < δ) (hδ₁ : δ < 1)
    (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
    (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
    (hD : Regeneration.annealedCoupledLaw Q.measure K
      (regenerationNoReturn hd (l / lam)) ≠ 0),
    (∀ (F : FieldPair d → ℝ),
      Measurable[localSigma {x : Vec d | euclideanNorm x < l / lam}] F →
      Regeneration.BoundedRealTest F →
      ∀ (Φ : Regeneration.FutureState d (Regeneration.Renewal.forceCoord hd) (l / lam) → ℝ),
      Measurable Φ → Regeneration.BoundedRealTest Φ → ∀ n : ℕ,
      ∀ μ ∈ ({Regeneration.annealedCoupledLaw Q.measure K,
        regenerationConditionedLaw hd Q lam l K hK.1 hD} :
          Set (Measure (FieldPair d × Regeneration.CoupledSample d))),
      (∫ ωz in {ωz | regenerationTime hd lam l 1 ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F ωz.1 * Φ (regenerationRecord hd lam l 1 ωz) ∂μ) =
      (∫ ωz in {ωz | regenerationTime hd lam l 1 ωz.2 =
        (((n : ℝ≥0) * Regeneration.Renewal.regenDelta lam : ℝ≥0) : ℝ≥0∞)},
        F ωz.1 ∂μ) *
      ∫ ωz, Φ (regenerationRecord hd lam l 0 ωz)
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ∧
    (∀ (m : ℕ) (H : Regeneration.CoupledSample d → ℝ),
      Measurable[Regeneration.finiteHistorySigma (Regeneration.Renewal.regenDelta lam) m] H →
      Regeneration.BoundedRealTest H → ∀ y : Vec d,
      ∃ A : FieldPair d → ℝ,
        Measurable[localSigma {x : Vec d |
          x (Regeneration.Renewal.forceCoord hd) ≤
            y (Regeneration.Renewal.forceCoord hd) - 4 * (l / lam)}] A ∧
        (fun ω => Regeneration.firstSlicePastIntegral
          (Regeneration.Renewal.regenDelta lam) lam (l / lam)
          (Regeneration.Renewal.forceCoord hd) m K H (y, ω)) =ᵐ[Q.measure] A)


end EinsteinFull.Blueprint.SbxCFactorizationR01
