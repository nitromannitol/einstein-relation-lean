import EinsteinFull.Frozen.JointObservation
import EinsteinFull.Frozen.ComplexTranslation
import EinsteinFull.Frozen.ReducedLawStationary
import Mathlib.Analysis.Distribution.SchwartzSpace.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The literal joint spatial test integral Z_R(F), taken in complex L².
Schwartz decay and the translation isometry give its genuine Bochner integral. -/
noncomputable def scaledJointPairing {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (R : ℝ) (_hR : 0 < R)
    (Z : JointObservationIndex d → Lp ℂ 2 (reducedLaw Q))
    (F : SchwartzMap (Vec d) (EuclideanSpace ℂ (JointObservationIndex d))) :
    Lp ℂ 2 (reducedLaw Q) :=
  ((R ^ (-(d : ℝ) / 2) : ℝ) : ℂ) •
    ∫ x : Vec d, ∑ a : JointObservationIndex d,
      F (R⁻¹ • x) a • complexTranslation (reducedLaw Q)
        (reducedLaw_stationary Q) x (Z a)

end EinsteinFull
