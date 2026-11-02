import EinsteinFull.Frozen.MobilityRate

/-!
# Theorem 1.2 (paper label `t.main`): the solution

The statement below is the statement of `Challenge.lean`, word for word. It is elaborated here
in the environment of the library, where the definitions that it uses are the library's own; the proof
applies the library theorem `EinsteinFull.Frozen.mobility_rate`.
-/

open MeasureTheory

namespace EinsteinFull.Frozen

open EinsteinRelation

theorem _root_.EinsteinFullAudit.MobilityRate.mobility_rate (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
    ∃ C lamStar : ℝ, 0 ≤ C ∧ 0 < lamStar ∧
      ∀ Q : EnvironmentLaw d D.ellipticity D.dependenceRange,
      HasSmoothBounds D Q →
      ∀ P : DiffusionFamily d,
      IsSignedPhysicalFamily (⟨0, by omega⟩ : Fin d) Q P →
      ∀ covariance : Mat d,
      HasDiffusivity Q.measure (originLaw (P 0)) covariance →
      ∀ (lam : ℝ), 0 < lam → lam ≤ lamStar →
      ∀ velocity : Vec d,
      HasQuenchedVelocity Q.measure (originLaw (P lam)) velocity →
        euclideanNorm ((lam⁻¹ • velocity) -
          covariance.mulVec (unitVector (⟨0, by omega⟩ : Fin d))) ≤ C * lam := by
  exact EinsteinFull.Frozen.mobility_rate d hd D

end EinsteinFull.Frozen
