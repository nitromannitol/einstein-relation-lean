import EinsteinRelation.External.AKMHeatKernel
import EinsteinRelation.Correctors.ParabolicRepresentative

open MeasureTheory Filter
open scoped Topology
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Positive-time scalar representatives preserve the actual fundamental
solution and its point-mass initial trace. Source: `paper/main.tex:787–792,850`. -/
theorem fundamentalSolution_scalar_congr_positive {d : ℕ} {K : ℝ}
    {A : Coefficient d K} {y : Vec d}
    {u v : ℝ × Vec d → ℝ} {G : ℝ × Vec d → Vec d}
    (hsol : IsFundamentalSolution A y u G)
    (huv : ∀ t : ℝ, 0 < t → ∀ x : Vec d, u (t,x) = v (t,x)) :
    IsFundamentalSolution A y v G := by
  refine ⟨?_,?_⟩
  · intro a b R ha hab hR
    have hball : IsOpen (originBall d R) := by
      apply isOpen_lt _ continuous_const
      unfold euclideanNorm euclideanSq dot
      fun_prop
    apply parabolicSolution_congr_ae hball (hsol.1 a b R ha hab hR)
    · filter_upwards [ae_restrict_mem (measurableSet_Ioo.prod
        (by change MeasurableSet {x : Vec d | euclideanNorm x < R}
            exact measurableSet_lt (by unfold euclideanNorm euclideanSq dot; fun_prop)
              measurable_const))] with z hz
      exact huv z.1 (ha.trans hz.1.1) z.2
    · exact Filter.EventuallyEq.rfl
  · intro ψ hψ
    apply (hsol.2 ψ hψ).congr'
    filter_upwards [self_mem_nhdsWithin] with t ht
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun x => congrArg (fun a : ℝ => a * ψ x) (huv t ht x)

end EinsteinRelation.Correctors
