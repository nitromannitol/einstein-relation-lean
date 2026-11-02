import EinsteinFull.Proofs.FiniteTimeUnforcedCommutator
import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.ReducedDriftObservation
import EinsteinFull.Frozen.FiniteTimeCommutator
import EinsteinFull.Frozen.JointObservation
import EinsteinFull.Frozen.CenteredComplexLp
import EinsteinFull.Frozen.GaussianDerivativeAverage

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Frozen
open EinsteinRelation

/-- Lemma 6.3: genuine finite-time corrector gradients and commutators, the
vector L2 approximation, and every fixed kernel derivative with a shared gain. -/
theorem finite_time_unforced_commutator (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ gain t₀ : ℝ, ∃ Cder : ℕ → ℝ,
      0 < gain ∧ 1 ≤ t₀ ∧ (∀ k, 0 < Cder k) ∧
    ∀ (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
      (hQ : HasSmoothBounds D Q)
      (β : Fin d → Lp ℂ 2 (reducedLaw Q))
      (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q)),
      IsReducedDriftObservation Q hQ β → IsJointObservation Q Z →
    ∀ P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q),
      ∀ hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P,
    ∃ G X : ℝ≥0 → Fin d → Fin d → Lp ℂ 2 (reducedLaw Q),
      (∀ (τ : ℝ≥0) (i : Fin d), IsFiniteTimeCommutator Q P hP.2.2.1 β τ i (G τ i) (X τ i)) ∧
      ∀ τ : ℝ≥0, t₀ ≤ (τ : ℝ) → ∀ s : ℝ, 2 * (τ : ℝ) ≤ s → ∀ hs : 0 < s,
      (∀ (i : Fin d) (k : ℕ) (dirs : Fin k → Fin d),
        Real.sqrt (∑ j : Fin d, ‖gaussianDerivativeAverage hd Q s hs k dirs
          (centeredComplexLp Q (X τ i j) - Z (.inl (j,i)))‖ ^ 2) ≤
          Cder k * (τ : ℝ) ^ (-gain) * s ^ (-(d : ℝ) / 4 - (k : ℝ) / 2)) ∧
      (∀ (i : Fin d) (k : ℕ), 1 ≤ k → ∀ dirs : Fin k → Fin d,
        ‖gaussianDerivativeAverage hd Q s hs k dirs (finiteTimeCorrector Q P hP.2.2.1 β τ i)‖ ≤
          Cder k * (τ : ℝ) * s ^ (-(1 / 2 + (d : ℝ) / 4) - (k : ℝ) / 2)) := by
  exact EinsteinFull.Proofs.finite_time_unforced_commutator d hd D

end EinsteinFull.Frozen
