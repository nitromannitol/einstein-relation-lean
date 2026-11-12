import EinsteinRelation.External.AKMLocalCorrectors
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Continuous spatial pairings of the actual positive-time flow

Source: `paper/main.tex:808-816`. Compactly supported tests turn the
joint continuity in the production semigroup contract into genuine
positive-time endpoint traces, without any assertion at time zero.
-/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Spatial test pairings of the actual scalar flow are continuous for
positive times. Source: `paper/main.tex:808-816`. -/
theorem akmLocal_semigroup_pairing_continuousOn {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {g : Vec d → Vec d}
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsSemigroupSolution A g u G)
    {ψ : Vec d → ℝ} (hψ : Continuous ψ) (hc : HasCompactSupport ψ) :
    ContinuousOn (fun t => ∫ x, u (t,x) * ψ x) (Set.Ioi 0) := by
  apply continuousOn_integral_of_compact_support hc.isCompact
  · exact hsol.1.mul (hψ.comp continuous_snd).continuousOn
  · intro t x _ hx
    rw [image_eq_zero_of_notMem_tsupport hx, mul_zero]

end EinsteinRelation.Correctors
