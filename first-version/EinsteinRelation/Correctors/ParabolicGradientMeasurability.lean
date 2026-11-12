import EinsteinRelation.External.AKMHeatKernel

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Local parabolic gradient measurability passes through a countable
exhaustion of space. Source: `paper/main.tex:787–792,850`. -/
theorem parabolic_gradient_aestronglyMeasurable {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {I : Set ℝ}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : ∀ R : ℝ, 0 < R → IsParabolicSolution A I (originBall d R) u G) :
    AEStronglyMeasurable G (volume.restrict (I ×ˢ Set.univ)) := by
  have hcover : (⋃ n : ℕ, I ×ˢ originBall d (n+1 : ℝ)) = I ×ˢ Set.univ := by
    ext z
    constructor
    · intro hz
      obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
      exact ⟨hn.1, Set.mem_univ _⟩
    · intro hz
      obtain ⟨n, hn⟩ := exists_nat_gt (euclideanNorm z.2)
      apply Set.mem_iUnion.mpr
      refine ⟨n, hz.1, ?_⟩
      change euclideanNorm z.2 < (n : ℝ)+1
      linarith
  rw [← hcover]
  exact aestronglyMeasurable_iUnion_iff.mpr (fun n => (hsol (n+1) (by positivity)).2.1)

end EinsteinRelation.Correctors
