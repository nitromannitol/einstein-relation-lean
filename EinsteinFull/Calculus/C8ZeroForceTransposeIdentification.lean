import EinsteinFull.Calculus.ComplexTransposeResolventSupport
import EinsteinFull.Frozen.TransposeEndpoint

open MeasureTheory Filter Set
open scoped NNReal ENNReal Topology
noncomputable section
namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- At zero force the bilinear transpose agrees with the forward semigroup. -/
theorem unforced_transpose_identification
    {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    : Pdag = P ∧ IsComplexTransposeSemigroup Q P P ∧
      ∀ (β : Fin d → Lp ℂ 2 (reducedLaw Q)) (t : ℝ≥0),
        transposeEndpoint Q i Pdag β t = P t (β i) := by
  have hforward : IsComplexEnvironmentSemigroup Q i 0 Pdag := by
    refine ⟨hPdag.zero hP, hPdag.add hP, hPdag.continuous_apply hP, ?_⟩
    intro f g
    exact (hPdag.tendsto_slope_iff hP f g).trans
      (isComplexTransposeGeneratorPair_zero_iff Q i f g)
  have heq : Pdag = P := hforward.unique hP
  refine ⟨heq, ?_, ?_⟩
  · simpa only [heq] using hPdag
  · intro β t
    simp only [transposeEndpoint, heq]

end EinsteinFull.Blueprint
