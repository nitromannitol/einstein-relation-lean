import EinsteinFull.Blueprint.G1.Draft.S3SmoothScope
import EinsteinFull.Blueprint.G1.node_rt_u3A_renewal_u23_cauchy
import EinsteinFull.Blueprint.G1.node_rt_u3A_many_u2D_cycle_u2D_moment
import EinsteinFull.Blueprint.Foundation.node_rt_u3A_renewal_u23_coupling_u2D_parameter_u2D_transfer

/-! Draft smooth-law statements; conditional and not reviewed or adopted. -/
open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint.SbxCRenewalR01
open EinsteinRelation EinsteinFull.Work.W5

def cauchySmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ ρ B c C : ℝ, 0 < ρ ∧ 0 < B ∧ 0 < c ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    let p := regenerationLatticeMass hd Q lam l K hK.1 hD
    let V := renewalRemovableDifference p
    AnalyticOnNhd ℂ V (Metric.closedBall 0 (1 + ρ)) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → ‖V z‖ ≤ B) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 + ρ → z ≠ 1 →
      V z = (1 - renewalGenerating p z)⁻¹ -
        ((renewalMean p : ℂ) * (1 - z))⁻¹) ∧
    (∀ n : ℕ, |(∑' j : ℕ, latticeConvolutionPower p j n) -
      (renewalMean p)⁻¹| ≤ C * Real.exp (-c * n))


def manyCycleSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ a M C : ℝ, 0 < a ∧ 0 < M ∧ 0 < C ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
      (P : QuenchedPathLaws d) (K : Regeneration.CoupledQuenchedLaws d)
      (hK : IsRegenerationCoupling hd Q lam l δ h₀.le h₁ P K)
      (hD : Regeneration.annealedCoupledLaw Q.measure K
        (regenerationNoReturn hd (l / lam)) ≠ 0),
    (∀ j : ℕ,
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a j ωz.2
        ∂regenerationConditionedLaw hd Q lam l K hK.1 hD) ≤ ENNReal.ofReal (M ^ j)) ∧
    (∀ j : ℕ,
      (∫⁻ ωz, regenerationExponentialWeight hd lam l a j ωz.2
        ∂Regeneration.annealedCoupledLaw Q.measure K) ≤ ENNReal.ofReal (C * M ^ j))


def couplingParameterTransferSmoothStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ l₀ : ℝ, 0 < l₀ ∧ D.dependenceRange < 2 * l₀ ∧
    ∀ l : ℝ, l₀ ≤ l → ∀ δ : ℝ, 0 < δ → δ < 1 →
    ∃ cD c C η : ℝ, ∃ N : ℕ,
      0 < cD ∧ 0 < c ∧ 0 < C ∧ 0 < η ∧ η ≤ 1 ∧ 0 < N ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (_hQ : HasSmoothBounds D Q) (lam : ℝ) (h₀ : 0 < lam) (h₁ : lam ≤ 1)
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


end EinsteinFull.Blueprint.SbxCRenewalR01
