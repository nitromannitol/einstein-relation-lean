import EinsteinRelation.Correctors.AKMParabolicIntegrability
import EinsteinRelation.Correctors.WeakEquationAveraging

/-! # Spatial gradients of finite-time parabolic integrals

Source: `paper/main.tex:808–816,844–848`. On a finite-volume spatial
domain, the corrected parabolic energy class gives the product
integrability needed to commute the actual spatial weak gradient with
time integration. This does not assume a time derivative or a strong
trace at time zero.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Finite-time integration of an actual energy-class parabolic solution
commutes with its spatial weak gradient. Source: `paper/main.tex:808–816`. -/
theorem parabolicSolution_integrated_gradient {d : ℕ} {K a b : ℝ}
    {A : Coefficient d K} {U : Set (Vec d)}
    [IsFiniteMeasure (volume.restrict U)]
    {u : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsParabolicSolution A (Set.Ioo a b) U u G) :
    HasWeakGradient U (fun x => ∫ t in Set.Ioo a b, u (t, x))
      (fun x j => ∫ t in Set.Ioo a b, G (t, x) j) := by
  let ν : Measure (ℝ × Vec d) := volume.restrict (Set.Ioo a b ×ˢ U)
  haveI : IsFiniteMeasure ν := by
    dsimp [ν]
    rw [Measure.volume_eq_prod ℝ (Vec d), ← Measure.prod_restrict]
    infer_instance
  have hu : Integrable u ν := hsol.1.integrable one_le_two
  have hG : ∀ j : Fin d, Integrable (fun z => G z j) ν := by
    intro j
    have hcoord : MemLp (fun z => G z j) 2 ν := by
      apply hsol.2.2.1.of_le
        ((continuous_apply j).comp_aestronglyMeasurable hsol.2.1)
      exact Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (show 0 ≤ euclideanNorm (G z) from Real.sqrt_nonneg _)]
        apply Real.abs_le_sqrt
        change G z j ^ 2 ≤ ∑ k : Fin d, G z k * G z k
        rw [sq]
        exact Finset.single_le_sum (fun k _ => mul_self_nonneg _) (Finset.mem_univ j)
    exact hcoord.integrable one_le_two
  apply hasWeakGradient_integral (volume.restrict (Set.Ioo a b)) U
    (fun t x => u (t, x)) (fun t x => G (t, x))
  · simpa only [ν, Measure.volume_eq_prod, Measure.prod_restrict] using hu
  · intro j
    simpa only [ν, Measure.volume_eq_prod, Measure.prod_restrict] using hG j
  · exact hsol.2.2.2.1

end EinsteinRelation.Correctors
