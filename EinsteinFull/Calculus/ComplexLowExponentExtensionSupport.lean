import EinsteinFull.Calculus.ComplexLpExtensionSupport

/-! The low-exponent estimates act on every datum of genuine Lp. -/
open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
namespace EinsteinFull

/-- The actual forward operator extends boundedly to the entire Lp space,
with the same leading constant one as its L2 restriction. -/
theorem IsComplexEnvironmentSemigroup.norm_LpExtension_below_two
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (t : ℝ≥0) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal hp.le)⟩
    ‖complexL2OperatorLpExtension (p := ENNReal.ofReal p) (reducedLaw Q)
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) (P t)‖ ≤
      Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
        (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀) * (Real.conjExponent p - 1)) ^ 2) * (t : ℝ)) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hp.le)⟩
  exact norm_complexL2OperatorLpExtension_le (reducedLaw Q) _ ENNReal.ofReal_ne_top
    (P t) (Real.exp_pos _).le (fun f => hP.eLpNorm_growth_below_two hp hp2 f t)

/-- The actual transpose has the same genuine low-Lp extension and retains
its independently proved forward-dual quadratic force rate. -/
theorem IsComplexTransposeSemigroup.norm_LpExtension_below_two
    {d : ℕ} {Λ₀ r₀ : ℝ} {Q : EnvironmentLaw d Λ₀ r₀} {i : Fin d} {ζ : ℂ}
    {P T : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i ζ P)
    (hT : IsComplexTransposeSemigroup Q P T)
    {p : ℝ} (hp : 1 < p) (hp2 : p ≤ 2) (t : ℝ≥0) :
    letI := reducedLaw_probability Q
    letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
      exact_mod_cast (ENNReal.ofReal_le_ofReal hp.le)⟩
    ‖complexL2OperatorLpExtension (p := ENNReal.ofReal p) (reducedLaw Q)
      (by exact_mod_cast (ENNReal.ofReal_le_ofReal hp2)) (T t)‖ ≤
      Real.exp (((d : ℝ) * (Real.exp (2 * Λ₀) * Λ₀) *
        (‖ζ‖ * (Real.exp (2 * Λ₀) * Λ₀)) ^ 2) * (t : ℝ)) := by
  letI := reducedLaw_probability Q
  letI : Fact (1 ≤ ENNReal.ofReal p) := ⟨by
    exact_mod_cast (ENNReal.ofReal_le_ofReal hp.le)⟩
  exact norm_complexL2OperatorLpExtension_le (reducedLaw Q) _ ENNReal.ofReal_ne_top
    (T t) (Real.exp_pos _).le (fun f => hT.eLpNorm_growth_below_two hP hp hp2 f t)

end EinsteinFull
