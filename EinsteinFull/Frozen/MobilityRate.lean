import EinsteinFull.Proofs.MobilityRate
import EinsteinFull.Frozen.StructuralData
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinFull.Frozen.SignedPhysicalFamily

open MeasureTheory

namespace EinsteinFull.Frozen

open EinsteinRelation

/-- Theorem 1.2: the uniform linear Einstein rate in the smooth class. -/
theorem mobility_rate (d : ℕ) (hd : 2 ≤ d) (D : StructuralData d) :
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
  exact EinsteinFull.Proofs.mobility_rate d hd D

end EinsteinFull.Frozen
