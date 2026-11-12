import EinsteinRelation.Correctors.ParabolicIntegratedGradient
import EinsteinRelation.Correctors.SpatialBallVolume
import EinsteinRelation.Calculus.WeakGradientExhaustion

/-! # Actual finite-time spatial potentials of the AKM flow

Source: `paper/main.tex:808-816`. Integrating an energy-class solution
between two positive times produces its actual spatial weak potential.
The ball-exhaustion argument makes this a whole-space identity. The
lower endpoint is kept positive, so no time-zero trace estimate is hidden.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- The finite-time scalar integral has the integrated actual PDE gradient
on the whole spatial domain. Source: `paper/main.tex:808-816`. -/
theorem akmLocal_semigroup_integrated_gradient {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    HasWeakGradient Set.univ (fun x => ∫ t in Set.Ioo a b, u (t, x))
      (fun x j => ∫ t in Set.Ioo a b, G (t, x) j) := by
  apply hasWeakGradient_univ_of_balls
  intro n
  have hR : 0 < (n : ℝ) + 1 := by positivity
  have hball : originBall d ((n : ℝ) + 1) = ball (0 : Vec d) ((n : ℝ) + 1) := by
    ext x
    simp only [originBall, ball, sub_zero]
  haveI : IsFiniteMeasure (volume.restrict (originBall d ((n : ℝ) + 1))) := by
    rw [hball]
    exact isFiniteMeasure_restrict.mpr
      (ENNReal.toReal_pos_iff.mp (ball_volume_pos_finite d _ hR)).2.ne
  have h := parabolicSolution_integrated_gradient (hsol.2.1 a b _ ha hab hR)
  simpa only [originBall, ball, sub_zero] using h

/-- The global finite-time potential identity holds for the same actual
coefficient-law scalar and gradient witnesses. Source: `paper/main.tex:808-816`. -/
theorem ae_akmLocal_semigroup_integrated_gradient {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K)) (g : Coefficient d K → Vec d → Vec d)
    (u : Coefficient d K → ℝ × Vec d → ℝ)
    (G : Coefficient d K → ℝ × Vec d → Vec d)
    (hsol : ∀ᵐ A ∂P, IsSemigroupSolution A (g A) (u A) (G A)) :
    ∀ᵐ A ∂P, ∀ a b : ℝ, 0 < a → a < b →
      HasWeakGradient Set.univ (fun x => ∫ t in Set.Ioo a b, u A (t, x))
        (fun x j => ∫ t in Set.Ioo a b, G A (t, x) j) := by
  filter_upwards [hsol] with A hA
  exact fun _ _ ha hab => akmLocal_semigroup_integrated_gradient hA ha hab

end EinsteinRelation.Correctors
