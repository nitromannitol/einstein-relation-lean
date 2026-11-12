import EinsteinRelation.Correctors.HeatGradientTranslation

/-! Source: `paper/main.tex:722,756`. The spatial source heat integral and
its time windows follow the actual translation action on environments. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

/-- Observing the stationary heat integral at `x` is the same as observing
it at the origin in the translated environment. -/
theorem akmHeatGradientSpaceIntegral_stationary_covariance {d : ℕ}
    (F : FieldPair d → Vec d) (ρ : FieldPair d) (t : ℝ)
    (j k l : Fin d) (x : Vec d) :
    akmHeatGradientSpaceIntegral (fun y => F (translate y ρ)) t j k l x =
      akmHeatGradientSpaceIntegral (fun y => F (translate y (translate x ρ)))
        t j k l 0 := by
  have h := akmHeatGradientSpaceIntegral_translation
    (fun y => F (translate y ρ)) x t j k l 0
  simpa only [zero_add, translate_add] using h.symm

/-- Every finite time window has the same exact environment covariance. -/
theorem setIntegral_akmHeatGradient_stationary_covariance {d : ℕ}
    (F : FieldPair d → Vec d) (ρ : FieldPair d) (s : Set ℝ)
    (j k l : Fin d) (x : Vec d) :
    (∫ t in s, akmHeatGradientSpaceIntegral (fun y => F (translate y ρ)) t j k l x) =
      ∫ t in s, akmHeatGradientSpaceIntegral
        (fun y => F (translate y (translate x ρ))) t j k l 0 := by
  simp only [akmHeatGradientSpaceIntegral_stationary_covariance F ρ]

end EinsteinRelation.Correctors
