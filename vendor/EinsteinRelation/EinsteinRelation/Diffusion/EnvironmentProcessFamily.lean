import EinsteinRelation.Diffusion.EnvironmentProcess

/-! # The reduced diffusion as an actual environment-process consumer

Source `paper/main.tex:250–252,430–437`. The physical coefficient pair remains
the environment carrier. It is the reduced path law that drives the observed
process. No invariant law, density or response estimate is assumed here.
-/

open MeasureTheory
open scoped NNReal

namespace EinsteinRelation

/-- Probability follows from the actual reduced martingale problem. -/
theorem IsReducedDiffusionFamily.probability {d : ℕ} {Λ₀ r₀ : ℝ} {i : Fin d}
    {Q : EnvironmentLaw d Λ₀ r₀} {P : DiffusionFamily d}
    (hP : IsReducedDiffusionFamily i Q P) {lam : ℝ} (hlam : 0 ≤ lam) :
    ∀ᵐ ω ∂Q.measure, IsProbabilityMeasure (originLaw (P lam) ω) := by
  filter_upwards [hP lam hlam] with ω hω
  exact hω.1

/-- The observed reduced diffusion has a genuine annealed probability law. -/
theorem IsReducedDiffusionFamily.annealedPathLaw_probability {d : ℕ} {Λ₀ r₀ : ℝ}
    {i : Fin d} {Q : EnvironmentLaw d Λ₀ r₀} {P : DiffusionFamily d}
    (hP : IsReducedDiffusionFamily i Q P) {lam : ℝ} (hlam : 0 ≤ lam) :
    IsProbabilityMeasure (EnvironmentProcess.annealedPathLaw Q.measure (P lam)) := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  exact EnvironmentProcess.annealedPathLaw_isProbabilityMeasure Q.measure (P lam)
    (hP.probability hlam)

/-- Each finite-time law is the literal environment observation pushforward. -/
theorem IsReducedDiffusionFamily.environmentTimeLaw_probability {d : ℕ} {Λ₀ r₀ : ℝ}
    {i : Fin d} {Q : EnvironmentLaw d Λ₀ r₀} {P : DiffusionFamily d}
    (hP : IsReducedDiffusionFamily i Q P) {lam : ℝ} (hlam : 0 ≤ lam) (t : ℝ≥0) :
    IsProbabilityMeasure (EnvironmentProcess.environmentTimeLaw Q.measure (P lam) t) := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  exact EnvironmentProcess.environmentTimeLaw_isProbabilityMeasure Q.measure (P lam)
    (hP.probability hlam) t

/-- Independent exponential time gives the actual mass-one occupation measure. -/
theorem IsReducedDiffusionFamily.resolventEnvironmentLaw_probability {d : ℕ} {Λ₀ r₀ : ℝ}
    {i : Fin d} {Q : EnvironmentLaw d Λ₀ r₀} {P : DiffusionFamily d}
    (hP : IsReducedDiffusionFamily i Q P) {lam : ℝ} (hlam : 0 ≤ lam)
    {s : ℝ} (hs : 0 < s) :
    IsProbabilityMeasure (EnvironmentProcess.resolventEnvironmentLaw Q.measure (P lam) s) := by
  letI : IsProbabilityMeasure Q.measure := Q.probability
  exact EnvironmentProcess.resolventEnvironmentLaw_isProbabilityMeasure Q.measure (P lam)
    (hP.probability hlam) s hs

end EinsteinRelation
