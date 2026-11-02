import EinsteinFull.Calculus.ComplexTransposeResolventSupport

open EinsteinRelation EinsteinFull MeasureTheory
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Blueprint

theorem c1_dyadic_zero_transpose_eq {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r}
    {i : Fin d}
    (P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q))
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (hPd : IsComplexTransposeSemigroup Q P Pdag) : Pdag = P := by
  have hforward : IsComplexEnvironmentSemigroup Q i 0 Pdag := by
    refine ⟨hPd.zero hP, hPd.add hP, hPd.continuous_apply hP, ?_⟩
    intro f g
    exact (hPd.tendsto_slope_iff hP f g).trans
      (isComplexTransposeGeneratorPair_zero_iff Q i f g)
  exact hforward.unique hP

end EinsteinFull.Blueprint
