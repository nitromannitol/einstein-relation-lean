import EinsteinFull.Regeneration.StationarySpaceTest
import PDEFoundation.PDE.WeakDivergenceForm
import PDEFoundation.Sobolev.Ch4.LipschitzH1

/-!
# Stationary lift of elliptic weak solutions

The `L²` divergence-form equation extends to compact `C¹` tests and hence
defines a time-independent parabolic weak solution.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- An elliptic `L²` weak solution is valid for compact `C¹` tests. -/
theorem elliptic_l2_solution_test_C1 {d : ℕ} {U : Set (PDE.Vec d)} (hU : IsOpen U)
    (a : PDE.CoeffField d) (u : PDE.H1Function U)
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn a U u 0 0)
    (ψ : PDE.Vec d → ℝ) (hψ : ContDiff ℝ 1 ψ) (hc : HasCompactSupport ψ)
    (hs : tsupport ψ ⊆ U) :
    IntegrableOn (fun x => PDE.vecDot (PDE.matVecMul (a x) (u.grad x))
      (PDE.spaceGradC1 ψ x)) U ∧
    (∫ x in U, PDE.vecDot (PDE.matVecMul (a x) (u.grad x))
      (PDE.spaceGradC1 ψ x)) = 0 := by
  obtain ⟨L, hL, hlip⟩ := PDE.Ch4Infra.EucLip.of_contDiff_hasCompactSupport hψ hc
  let η := PDE.Ch4Infra.lipH10 hU hlip hL hc hs
  obtain ⟨hint, heq⟩ := hsol.toH10SolutionOn η
  have hgrad : η.toH1Function.grad = PDE.spaceGradC1 ψ := rfl
  refine ⟨?_, ?_⟩
  · simpa only [hgrad] using hint.flux_integrable
  · simpa only [hgrad, Pi.zero_apply, zero_mul, PDE.vecDot, Finset.sum_const_zero,
      integral_zero, sub_zero] using heq

/-- An elliptic `L²` weak solution lifts to a stationary parabolic weak solution. -/
theorem elliptic_l2_solution_stationary {d : ℕ} {U : Set (PDE.Vec d)} (hU : IsOpen U)
    (I : Set ℝ) [IsFiniteMeasure (volume.restrict I : Measure ℝ)]
    (a : PDE.CoeffField d) (u : PDE.H1Function U)
    (hsol : PDE.IsWeakDivergenceFormL2SolutionOn a U u 0 0) :
    PDE.IsParabolicWeakSolution (fun z => a z.1) U I
      (stationaryParH1 U I u.toFun u.grad u.memL2 u.gradMemL2 u.hasWeakGradient) := by
  apply stationary_isParabolicWeakSolution U I u.toFun u.grad a u.memL2 u.gradMemL2
    u.hasWeakGradient hsol.flux_memL2
  exact elliptic_l2_solution_test_C1 hU a u hsol

end EinsteinFull.Regeneration
