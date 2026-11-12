import EinsteinRelation.Correctors.SemigroupPrescribedGradient
import EinsteinRelation.Correctors.PrescribedBallCutoff

/-! # Whole-space positive-time weak gradients without auxiliary premises

Source: `paper/main.tex:798–806`. Smooth cutoffs are constructed internally.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Every positive-time scalar slice of an actual autonomous semigroup
solution has a whole-space weak gradient. Source: `paper/main.tex:798–806`. -/
theorem semigroupSolution_exists_positive_time_gradient {d : ℕ} {K : ℝ}
    (hK : 0 < K) {A : Coefficient d K} {v : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A v u G) {t : ℝ} (ht : 0 < t) :
    ∃ H : Vec d → Vec d, HasWeakGradient Set.univ (fun x => u (t,x)) H :=
  semigroupSolution_exists_prescribed_gradient hK
    (exists_prescribed_spatial_ball_cutoff d) hsol ht

/-- One jointly measurable field realizes the actual weak gradient of
all positive-time scalar slices on the semigroup event.
Source: `paper/main.tex:798–806`. -/
theorem exists_measurable_positive_time_gradient {Ω : Type*} [MeasurableSpace Ω]
    {d : ℕ} {K : ℝ} (hK : 0 < K)
    (P : Measure Ω) (A : Ω → Coefficient d K) (v : Ω → Vec d → Vec d)
    (u : Ω → ℝ × Vec d → ℝ) (G : Ω → ℝ × Vec d → Vec d)
    (hum : Measurable (fun z : Ω × (ℝ × Vec d) => u z.1 z.2))
    (hsol : ∀ᵐ ω ∂P, IsSemigroupSolution (A ω) (v ω) (u ω) (G ω)) :
    ∃ H : Ω → ℝ × Vec d → Vec d,
      Measurable (fun z : Ω × (ℝ × Vec d) => H z.1 z.2) ∧
      ∀ᵐ ω ∂P, ∀ t : ℝ, 0 < t →
        HasWeakGradient Set.univ (fun x => u ω (t,x)) (fun x => H ω (t,x)) :=
  measurable_prescribed_gradient_of_semigroupSolutions hK
    (exists_prescribed_spatial_ball_cutoff d) P A v u G hum hsol

end EinsteinRelation.Correctors
