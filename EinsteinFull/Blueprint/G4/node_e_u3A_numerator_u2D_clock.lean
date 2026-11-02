import EinsteinFull.Blueprint.Roots.node_p_u3A_profile
import EinsteinFull.Frozen.IntegratedKernelCoefficient
import EinsteinFull.Frozen.IntegratedKernelCriticalCoefficient
import EinsteinFull.Frozen.CriticalKernelTerm
import EinsteinFull.Frozen.ExpansionModulus
import EinsteinFull.Frozen.ReducedClockRate

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:numerator-clock`, `paper/main.tex:1402–1411`.
The prescribed integrated coefficients define the ordinary numerator and
clock coefficients before path realizations and signed force. Both remainders
use the same structural constants and the clock constant coefficient is zero. -/
def node_e_u3A_numerator_u2D_clockStmt : Prop :=
  ∀ (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d),
    ∃ C lamStar : ℝ, 0 < C ∧ 0 < lamStar ∧ lamStar ≤ Real.exp (-1) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q))
      (μ : Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
      (covariance : Matrix (JointObservationIndex d) (JointObservationIndex d) ℝ),
      IsReducedDriftObservation Q hQ β → IsReducedCoefficientObservation Q a →
      IsReducedClockObservation Q μ → IsJointObservation Q Z →
      IsJointCovariance Q Z covariance →
      ∀ P : ℂ → ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      (∀ z : ℂ, IsComplexEnvironmentSemigroup Q (⟨0, by omega⟩ : Fin d) z (P z)) →
      let first : Fin d := ⟨0, by omega⟩
      let A := homogenizedCoefficient Q
      let p₀ : ℝ := (2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt A.det
      let γ : ℝ := A first first / 2
      let u₀ : Option (Fin d) → ℝ := fun κ => match κ with
        | none => 0
        | some i => p₀ / 4 * ∑ j, ∑ k,
            (A⁻¹) j k * covariance (.inl (j, first)) (.inl (k, i))
      let u₂ : Option (Fin d) → ℝ := fun κ => match κ with
        | none => p₀ / 2 * covariance (.inl (first, first)) (.inr ())
        | some i => p₀ / 4 * covariance (.inl (first, first)) (.inl (first, i))
      let K : Option (Fin d) → ℝ → ℂ → ℂ := fun κ t z => match κ with
        | none => clockCorrelation Q first z (P z) β μ t.toNNReal
        | some i => velocityCorrelation Q first i z (P z) β a t.toNNReal
      ∃ (hγ : 0 < γ)
        (hK : ∀ (κ : Option (Fin d)) (t : ℝ), 0 ≤ t → Differentiable ℂ (K κ t))
        (hR : ∀ (κ : Option (Fin d)) (t : ℝ), 0 ≤ t →
          ∀ lam : ℝ, (K κ t (lam : ℂ)).im = 0)
        (hI : ∀ (κ : Option (Fin d)) (j : Fin (d + 1)),
          IntegrableOn (fun t : ℝ => iteratedDeriv j.val (fun lam : ℝ =>
            (kernelProfileRemainder d (u₀ κ) (u₂ κ) γ (K κ) t (lam : ℂ)).re) 0 /
              (j.val.factorial : ℝ)) (Set.Ici 0)),
      let k : Option (Fin d) → Fin (d + 1) → ℝ := fun κ =>
        integratedKernelCoefficient d (u₀ κ) (u₂ κ) γ hγ (K κ) (hK κ) (hR κ) (hI κ)
      let χ : Option (Fin d) → ℝ := fun κ =>
        integratedKernelCriticalCoefficient d (u₀ κ) (u₂ κ) γ hγ
      let m : ℝ := ∫ ω, ω.2 0 ∂reducedLaw Q
      let aCoeff : Fin (d + 1) → Vec d := fun n i =>
        if n.val = 0 then (∫ ω, ω.1 0 first i ∂reducedLaw Q) - 2 * k (some i) ⟨0, by omega⟩
        else -2 * k (some i) n
      let etaCoeff : Fin d → ℝ := fun j => -2 * k none ⟨j.val + 1, by omega⟩
      k none ⟨0, by omega⟩ = 0 ∧
      (∀ n : Fin (d + 1), euclideanNorm (aCoeff n) ≤ C) ∧
      (∀ j : Fin d, |etaCoeff j| ≤ C) ∧
      euclideanNorm (fun i => χ (some i)) + |χ none| ≤ C ∧
      ∀ (lam : ℝ) (h₀ : 0 < |lam|) (h₁ : |lam| ≤ lamStar)
        (hsmall : |lam| ≤ Real.exp (-1)) (Y : QuenchedPathLaws d),
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator first ω lam) 0 (Y (0, ω))) →
      ∀ (ell : Vec d) (η : ℝ),
      HasQuenchedVelocity Q.measure (originLaw Y) ell → HasReducedClockRate Q Y η →
        euclideanNorm (ell - (∑ n : Fin (d + 1), lam ^ (n.val + 1) • aCoeff n) +
          (2 * lam * criticalKernelTerm d lam (abs_pos.mp h₀)) •
            (fun i => χ (some i))) ≤
          C * |lam| ^ (d + 1) * expansionModulus |lam| h₀ hsmall ∧
        |η - m - (∑ j : Fin d, etaCoeff j * lam ^ (j.val + 1)) +
          2 * χ none * criticalKernelTerm d lam (abs_pos.mp h₀)| ≤
          C * |lam| ^ d * expansionModulus |lam| h₀ hsmall

end EinsteinFull.Blueprint
