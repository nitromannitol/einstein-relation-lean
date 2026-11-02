import EinsteinFull.Blueprint.G4.node_e_u3A_numerator_u2D_clock
import EinsteinFull.Frozen.CriticalVelocityTerm
import EinsteinFull.Frozen.SignedPhysicalFamily

open MeasureTheory Filter
open scoped Topology NNReal BigOperators

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Graph node `e:division`, `paper/main.tex:1413–1424`.
The coefficients unfold the literal integratedKernelCoefficient formula of the
actual law. Index n is the paper coefficient n+1 for a and b; recip n is D_n.
The reciprocal recursion and singular coefficient precede all path realizations
and signed forces. The integral formula is definitionally the frozen coefficient
for every set of its analytic proof arguments; these proofs do not occur in its
value. No numerator/clock conclusion is made an extra premise. -/
def node_e_u3A_divisionStmt : Prop :=
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
      (∀ z : ℂ, IsComplexEnvironmentSemigroup Q (⟨0, lt_of_lt_of_le (by decide : 0 < 2) hd⟩ : Fin d) z (P z)) →
      let first : Fin d := ⟨0, lt_of_lt_of_le (by decide : 0 < 2) hd⟩
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
      ∃ hγ : 0 < γ,
      let k : Option (Fin d) → Fin (d + 1) → ℝ := fun κ n =>
        (∫ t in Set.Ici (0 : ℝ), iteratedDeriv n.val (fun lam : ℝ =>
          (kernelProfileRemainder d (u₀ κ) (u₂ κ) γ (K κ) t (lam : ℂ)).re) 0 /
            (n.val.factorial : ℝ)) +
          if n.val < d then 2 * profileTaylorCoefficient (u₀ κ) (u₂ κ) γ n.val /
            ((d - n.val : ℕ) : ℝ)
          else if Even d then 2 * profileFinitePart d (u₀ κ) (u₂ κ) γ hγ else 0
      let χ : Option (Fin d) → ℝ := fun κ =>
        integratedKernelCriticalCoefficient d (u₀ κ) (u₂ κ) γ hγ
      let m : ℝ := ∫ ω, ω.2 0 ∂reducedLaw Q
      let aCoeff : Fin (d + 1) → Vec d := fun n i =>
        if n.val = 0 then (∫ ω, ω.1 0 first i ∂reducedLaw Q) - 2 * k (some i) ⟨0, Nat.zero_lt_succ d⟩
        else -2 * k (some i) n
      let etaCoeff : Fin d → ℝ := fun j => -2 * k none ⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩
      (fun (aCoeff : Fin (d + 1) → Vec d) (etaCoeff : Fin d → ℝ)
        (χ : Option (Fin d) → ℝ) (m : ℝ) (A : Mat d) =>
      ∃ (recip : Fin (d + 1) → ℝ) (b : Fin (d + 1) → Vec d) (c : Vec d),
        aCoeff ⟨0, Nat.zero_lt_succ d⟩ = A.mulVec (unitVector first) ∧
        recip ⟨0, Nat.zero_lt_succ d⟩ = m⁻¹ ∧
        (∀ n : Fin (d + 1), n.val ≠ 0 →
          recip n = -m⁻¹ * ∑ j : Fin n.val,
            etaCoeff ⟨j.val, Nat.lt_of_lt_of_le j.isLt (Nat.le_of_lt_succ n.isLt)⟩ * recip ⟨n.val - (j.val + 1), Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩) ∧
        (∀ n : Fin (d + 1), b n = ∑ k : Fin (n.val + 1),
          recip ⟨n.val - k.val, Nat.lt_of_le_of_lt (Nat.sub_le _ _) n.isLt⟩ • aCoeff ⟨k.val, Nat.lt_of_lt_of_le k.isLt n.isLt⟩) ∧
        c = (fun i => (-2 / m) * χ (some i) +
          (2 * χ none / m ^ 2) * (A.mulVec (unitVector first)) i) ∧
        (∑ n, |recip n|) + (∑ n, euclideanNorm (b n)) + euclideanNorm c ≤ C ∧
        b ⟨0, Nat.zero_lt_succ d⟩ = m⁻¹ • A.mulVec (unitVector first) ∧
        (∀ X : DiffusionFamily d, IsSignedPhysicalFamily first Q X →
          ∀ covariance : Mat d, HasDiffusivity Q.measure (originLaw (X 0)) covariance →
            b ⟨0, Nat.zero_lt_succ d⟩ = covariance.mulVec (unitVector first)) ∧
        ∀ (lam : ℝ) (h₀ : 0 < |lam|) (h₁ : |lam| ≤ lamStar)
          (hsmall : |lam| ≤ Real.exp (-1)) (Y : QuenchedPathLaws d),
          (∀ᵐ ω ∂Q.measure,
            SolvesMartingaleProblem (reducedGenerator first ω lam) 0 (Y (0, ω))) →
          ∀ (ell : Vec d) (η : ℝ),
            HasQuenchedVelocity Q.measure (originLaw Y) ell → HasReducedClockRate Q Y η →
              C⁻¹ ≤ m ∧ C⁻¹ ≤ η ∧ η ≤ C ∧
              |η⁻¹ - (∑ n : Fin (d + 1), recip n * lam ^ n.val) -
                (2 * χ none / m ^ 2) * criticalKernelTerm d lam (abs_pos.mp h₀)| ≤
                C * |lam| ^ d * expansionModulus |lam| h₀ hsmall ∧
              euclideanNorm (η⁻¹ • ell - (∑ n : Fin (d + 1), lam ^ (n.val + 1) • b n) -
                criticalVelocityTerm d lam (abs_pos.mp h₀) • c) ≤
                C * |lam| ^ (d + 1) * expansionModulus |lam| h₀ hsmall ∧
              |lam| ^ (d + 2) * (1 + Real.log (1 / |lam|)) ^ 2 ≤
                C * |lam| ^ (d + 1) * expansionModulus |lam| h₀ hsmall
      ) aCoeff etaCoeff χ m A

end EinsteinFull.Blueprint
