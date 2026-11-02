import EinsteinRelation.Environment.AKMTestIntegralSupport
import Mathlib.Analysis.Distribution.AEEqOfIntegralContDiff

/-!
# Faithfulness of AKM coefficient observations

Source: `paper/main.tex:693-698` and AKM (0.11). Equality of all smooth
test-integral observations determines the coefficient almost everywhere,
including coefficients without continuous pointwise representatives.
-/

open MeasureTheory
namespace EinsteinRelation.Environment.AKMTestIntegralSupport

/-- AKM test observations determine the actual locally integrable matrix
field up to spatial null sets. -/
theorem coefficient_field_ae_eq_of_testIntegral_eq {d : ℕ} {K : ℝ}
    (a b : Coefficient d K)
    (h : ∀ (u : SmoothCompactTest d) (i j : Fin d),
      testIntegral a u i j = testIntegral b u i j) :
    a.field =ᵐ[volume] b.field := by
  have hc (i j : Fin d) : ∀ᵐ x ∂volume, a.field x i j = b.field x i j := by
    apply ae_eq_of_integral_contDiff_smul_eq
      (a.locally_integrable i j) (b.locally_integrable i j)
    intro φ hφ hφc
    simpa only [testIntegral, smul_eq_mul] using h ⟨φ, hφ, hφc⟩ i j
  filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hc i))] with x hx
  ext i j
  exact hx i j

end EinsteinRelation.Environment.AKMTestIntegralSupport
