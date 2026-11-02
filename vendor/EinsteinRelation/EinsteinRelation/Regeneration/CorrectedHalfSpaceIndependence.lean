import EinsteinRelation.Regeneration.HalfSpaces
import EinsteinRelation.Regeneration.RenewalFromInputs

/-!
# The finite-range step for the corrected half-spaces

Source `paper/main.tex:399–403`. The past observes coordinates at most
`yᵢ - 4R`, and the future observes coordinates at least `yᵢ - 2R`.
The actual joint finite-range assumption separates these sigma-algebras
when `r₀ < 2R`. Local a.e. versions suffice for factorization.
-/

open MeasureTheory

namespace EinsteinRelation.Regeneration

/-- The two half-spaces in Step 3 are independent under the actual joint
environment law. -/
theorem indep_corrected_halfSpaces {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (y R : ℝ) (hgap : r₀ < 2 * R) :
    ProbabilityTheory.Indep (localSigma {x : Vec d | x i ≤ y - 4 * R})
      (localSigma {x : Vec d | y - 2 * R ≤ x i}) Q.measure := by
  apply Q.finiteRange _ _
    (measurableSet_le (measurable_pi_apply i) measurable_const)
    (measurableSet_le measurable_const (measurable_pi_apply i))
  exact ⟨2 * R, hgap, fun x hx z hz => corrected_halfSpace_gap i x z y R hx hz⟩

/-- A.e. local versions give exactly the product identity needed by
`regen.slice-factor`; no pointwise local version at exceptional environments
is required (`paper/main.tex:399–403`). -/
theorem integral_mul_eq_of_corrected_halfSpace_versions {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (y R : ℝ) (hgap : r₀ < 2 * R)
    (A B A' B' : FieldPair d → ℝ)
    (hA : Measurable[localSigma {x : Vec d | x i ≤ y - 4 * R}] A')
    (hB : Measurable[localSigma {x : Vec d | y - 2 * R ≤ x i}] B')
    (hAe : A =ᵐ[Q.measure] A') (hBe : B =ᵐ[Q.measure] B') :
    (∫ ω, A ω * B ω ∂Q.measure) =
      (∫ ω, A ω ∂Q.measure) * ∫ ω, B ω ∂Q.measure := by
  calc
    _ = ∫ ω, A' ω * B' ω ∂Q.measure := integral_congr_ae (hAe.mul hBe)
    _ = (∫ ω, A' ω ∂Q.measure) * ∫ ω, B' ω ∂Q.measure :=
      Renewal.integral_mul_eq_of_indep_localSigma Q.measure _ _
        (indep_corrected_halfSpaces Q i y R hgap) A' B' hA hB
    _ = _ := by rw [integral_congr_ae hAe, integral_congr_ae hBe]


end EinsteinRelation.Regeneration
