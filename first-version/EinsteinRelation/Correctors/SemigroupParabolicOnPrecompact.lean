import EinsteinRelation.Correctors.ParabolicSolutionSpatialRestriction
import EinsteinRelation.Correctors.AKMHeatKernelSpatialExhaustion

/-! # The semigroup weak equation on relatively compact domains

Source: `paper/main.tex:816–832`. The actual semigroup equation on
Euclidean balls restricts to any relatively compact open spatial set.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- No extra local PDE hypothesis is needed on a relatively compact open
set for the actual semigroup solution. Source: `paper/main.tex:816–832`. -/
theorem semigroupSolution_parabolic_on_precompact
    {d : ℕ} {K : ℝ} {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {U : Set (Vec d)} (hU : IsOpen U) (hUc : IsCompact (closure U))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    IsParabolicSolution A (Set.Ioo a b) U u G := by
  obtain ⟨N, hN⟩ := akm_compact_subset_originBall hUc
  have hc : Continuous (fun x : Vec d => euclideanNorm x) := by
    unfold euclideanNorm euclideanSq dot
    fun_prop
  have hball : IsOpen (originBall d (N + 1 : ℝ)) := isOpen_lt hc continuous_const
  exact parabolicSolution_spatial_restrict measurableSet_Ioo hball.measurableSet
    hU.measurableSet (subset_closure.trans hN)
      (hsol.2.1 a b (N + 1 : ℝ) ha hab (by positivity))

end EinsteinRelation.Correctors
