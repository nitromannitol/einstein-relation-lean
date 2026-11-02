import EinsteinFull.Calculus.ComplexLpNormingSupport
import EinsteinFull.Calculus.RadialTransposeCutoffLimitSupport

/-! Bilinear duality supplies the stationary growth bounds for 1 < p ≤ 2. -/
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull

private theorem two_le_conjExponent {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) :
    2 ≤ Real.conjExponent p := by
  rw [Real.conjExponent, le_div_iff₀ (by linarith : 0 < p - 1)]
  linarith

/-- Forward growth below two, with the actual conjugate exponent in the rate.
No extra transpose or norm-representation hypothesis is needed. -/
theorem IsComplexEnvironmentSemigroup.eLpNorm_growth_below_two
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    eLpNorm (P t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
      eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) *
        ENNReal.ofReal (Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (Real.conjExponent p - 1)) ^ 2) *
            (t : ℝ))) := by
  letI := reducedLaw_probability Q
  let q := Real.conjExponent p
  have hq : 2 ≤ q := two_le_conjExponent hp hp2
  have ha : 0 ≤ q / 2 - 1 := by linarith
  have he : 2 * (1 + (q / 2 - 1)) = q := by ring
  have he' : 1 + 2 * (q / 2 - 1) = q - 1 := by ring
  apply eLpNorm_le_of_complexL2Transpose_bound (reducedLaw Q) (P t)
    (Real.HolderConjugate.conjExponent hp) hp2 hq (Real.exp_pos _).le
  intro g hg
  have ht := isComplexTransposeSemigroup_complexL2Transpose Q P
  have hbound := ht.eLpNorm_growth hP ha g (by simpa only [he] using hg) t
  simpa only [he, he'] using hbound

/-- Transpose growth below two follows from the proved forward high-exponent
bound and involutivity of the actual bilinear transpose. -/
theorem IsComplexTransposeSemigroup.eLpNorm_growth_below_two
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2)
    (f : Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0) :
    eLpNorm (T t f) (ENNReal.ofReal p) (reducedLaw Q) ≤
      eLpNorm f (ENNReal.ofReal p) (reducedLaw Q) *
        ENNReal.ofReal (Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
          (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) * (t : ℝ))) := by
  letI := reducedLaw_probability Q
  let q := Real.conjExponent p
  have hq : 2 ≤ q := two_le_conjExponent hp hp2
  have ha : 0 ≤ q / 2 - 1 := by linarith
  have he : 2 * (1 + (q / 2 - 1)) = q := by ring
  apply eLpNorm_le_of_complexL2Transpose_bound (reducedLaw Q) (T t)
    (Real.HolderConjugate.conjExponent hp) hp2 hq (Real.exp_pos _).le
  intro g hg
  have hbound := hP.eLpNorm_growth ha g (by simpa only [he] using hg) t
  simpa only [hT.eq_complexL2Transpose, complexL2Transpose_involutive, he] using hbound

end EinsteinFull
