import EinsteinFull.External.Draft.DFGWInvarianceV2

/-! # Brownian law with zero covariance

The zero path gives the Brownian law associated with the zero covariance matrix, including in
zero dimensions.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation

namespace EinsteinFull.External.DFGW

/-- The Dirac mass at the zero path is a Brownian law with zero covariance. -/
theorem isBrownianLaw_zero_dirac (d : ℕ) :
    IsBrownianLaw (0 : Mat d) (Measure.dirac (0 : Path d)) := by
  refine ⟨inferInstance, by simp, ?_, ?_, ?_⟩
  · intro e
    simp [dot]
  · simp
  · intro n t ξ
    simp [dot, integral_dirac]

end EinsteinFull.External.DFGW
