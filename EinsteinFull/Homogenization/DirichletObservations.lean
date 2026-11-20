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

/-- On an open domain, local test observations determine the Dirichlet energy. -/
theorem sourceDirichletEnergy_eq_of_local_testIntegral_eq {d : ℕ} {K : ℝ}
    (a b : Coefficient d K) (U : Set (Vec d)) (hU : IsOpen U) (e : Vec d)
    (h : ∀ (u : SmoothCompactTest d), tsupport u.toFun ⊆ U → ∀ i j : Fin d,
      testIntegral a u i j = testIntegral b u i j) :
    sourceDirichletEnergy a U e = sourceDirichletEnergy b U e := by
  apply sourceDirichletEnergy_eq_of_ae_eq
  have hc (i j : Fin d) : ∀ᵐ x ∂volume.restrict U, a x i j = b x i j := by
    rw [ae_restrict_iff' hU.measurableSet]
    have hz := hU.ae_eq_zero_of_integral_contDiff_smul_eq_zero
      (((a.locally_integrable i j).sub (b.locally_integrable i j)).locallyIntegrableOn U)
      (fun φ hφ hφc hφU => by
        have hi := integrable_testIntegrand a ⟨φ, hφ, hφc⟩ i j
        have hj := integrable_testIntegrand b ⟨φ, hφ, hφc⟩ i j
        change (∫ x, φ x * (a x i j - b x i j) ∂volume) = 0
        simp only [mul_sub, integral_sub hi hj]
        exact sub_eq_zero.mpr (h ⟨φ, hφ, hφc⟩ hφU i j))
    filter_upwards [hz] with x hx hxU
    exact sub_eq_zero.mp (hx hxU)
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hc i))] with x hx
  ext i j
  exact hx i j

end EinsteinFull.Homogenization
