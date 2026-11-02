import EinsteinFull.Frozen.UniformSmallForceExpansion

/-!
# Theorem 1.1 (paper label `t:expansion`): the solution

The statement below is the statement of `Challenge.lean`, word for word. It is elaborated here
in the environment of the library, where the definitions that it uses are the library's own; the proof
applies the library theorem `EinsteinFull.Frozen.uniform_small_force_expansion`.
-/

open MeasureTheory
open scoped BigOperators

namespace EinsteinFull.Frozen

open EinsteinRelation

theorem _root_.EinsteinFullAudit.UniformSmallForceExpansion.uniform_small_force_expansion (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C lamStar : ℝ, 0 ≤ C ∧ 0 < lamStar ∧
      ∃ hstar : lamStar ≤ Real.exp (-1),
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∃ (b : Fin (d + 1) → Vec d) (c : Vec d),
        (∑ j, euclideanNorm (b j)) + euclideanNorm c ≤ C ∧
        ∀ P : DiffusionFamily d,
        IsSignedPhysicalFamily (⟨0, by omega⟩ : Fin d) Q P →
        ∀ covariance : Mat d,
        HasDiffusivity Q.measure (originLaw (P 0)) covariance →
          b ⟨0, by omega⟩ = covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d)) ∧
          ∀ velocity : ℝ → Vec d,
          (∀ lam : ℝ, lam ≠ 0 →
            HasQuenchedVelocity Q.measure (originLaw (P lam)) (velocity lam)) →
          ∀ (lam : ℝ) (hlam : 0 < |lam|) (hsmall : |lam| ≤ lamStar),
            euclideanNorm (velocity lam - (∑ j : Fin (d + 1), lam ^ (j.val + 1) • b j) -
              criticalVelocityTerm d lam (abs_pos.mp hlam) • c) ≤
              C * |lam| ^ (d + 1) *
                expansionModulus |lam| hlam (hsmall.trans hstar) := by
  exact EinsteinFull.Frozen.uniform_small_force_expansion d hd D

end EinsteinFull.Frozen
