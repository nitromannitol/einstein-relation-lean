import EinsteinFull.Homogenization.DirichletLocality
import EinsteinRelation.Environment.AKMCoefficientObservationUniqueness

/-!
# Dirichlet energy and coefficient observations

The energy μ of Armstrong, Kuusi and Mourrat, (1.7), is determined by the
smooth test-integral observations of the coefficient field.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Coefficients with the same smooth observations have equal Dirichlet energies. -/
theorem sourceDirichletEnergy_eq_of_testIntegral_eq {d : ℕ} {K : ℝ}
    (a b : Coefficient d K) (U : Set (Vec d)) (e : Vec d)
    (h : ∀ (u : SmoothCompactTest d) (i j : Fin d),
      testIntegral a u i j = testIntegral b u i j) :
    sourceDirichletEnergy a U e = sourceDirichletEnergy b U e :=
  sourceDirichletEnergy_eq_of_ae_eq a b U e
    (ae_restrict_of_ae (coefficient_field_ae_eq_of_testIntegral_eq a b h))

end EinsteinFull.Homogenization
