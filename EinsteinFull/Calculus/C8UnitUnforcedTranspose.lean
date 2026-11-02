import EinsteinFull.Calculus.ComplexTransposeResolventSupport
import EinsteinFull.Frozen.TransposeEndpoint
import EinsteinFull.Calculus.C7UnitInitializationSupport

/-! The zero-force transpose identification needed for unit initialization.
The Gaussian estimate awaits the forward unforced drift estimate. -/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

-- Anonymous internal bridge for the assigned unit_unforced_transpose_gaussian.
-- The full zero-force weak graphs coincide, so uniqueness applies to the
-- actual bilinear transpose without replacing it by a Hermitian adjoint.
example {d : ℕ} {Λ r : ℝ} {Q : EnvironmentLaw d Λ r} {i : Fin d}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q i 0 P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag) :
    Pdag = P ∧ IsComplexTransposeSemigroup Q P P ∧
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

-- The actual transpose endpoint has the same centered physical flux bracket,
-- including at time zero, where the bracket is the coefficient column itself.
example {d : ℕ} (hd : 2 ≤ d) {D : StructuralData d}
    {Q : EnvironmentLaw d D.ellipticity D.dependenceRange}
    {hQ : HasSmoothBounds D Q}
    {P Pdag : ℝ≥0 → Lp ℂ 2 (reducedLaw Q) →L[ℂ] Lp ℂ 2 (reducedLaw Q)}
    (hP : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 P)
    (hPdag : IsComplexTransposeSemigroup Q P Pdag)
    {β : Fin d → Lp ℂ 2 (reducedLaw Q)} (hβ : IsReducedDriftObservation Q hQ β)
    {a : Fin d → Fin d → Lp ℂ 2 (reducedLaw Q)}
    (ha : IsReducedCoefficientObservation Q a) (s : ℝ) (hs : 0 < s) :
    (∀ t : ℝ≥0,
      let F := fun l => a l ⟨0, by omega⟩ +
        ∫ r in Set.Icc (0 : ℝ) (t : ℝ), ∑ k,
          complexCoefficientMul Q l k (hP.gradientOrbit (β ⟨0, by omega⟩) r k)
      gaussianAverage hd Q s hs (transposeEndpoint Q ⟨0, by omega⟩ Pdag β t) =
        (1 / 2 : ℝ) • ∑ l, gaussianDerivativeAverage hd Q s hs 1
          (fun _ => l) (centeredComplexLp Q (F l))) ∧
    gaussianAverage hd Q s hs (transposeEndpoint Q ⟨0, by omega⟩ Pdag β 0) =
      (1 / 2 : ℝ) • ∑ l, gaussianDerivativeAverage hd Q s hs 1
        (fun _ => l) (centeredComplexLp Q (a l ⟨0, by omega⟩)) := by
  have hforward : IsComplexEnvironmentSemigroup Q ⟨0, by omega⟩ 0 Pdag := by
    refine ⟨hPdag.zero hP, hPdag.add hP, hPdag.continuous_apply hP, ?_⟩
    intro f g
    exact (hPdag.tendsto_slope_iff hP f g).trans
      (isComplexTransposeGeneratorPair_zero_iff Q ⟨0, by omega⟩ f g)
  have heq : Pdag = P := hforward.unique hP
  have hflux := fun t => EinsteinFull.UnitInitialization.unforced_gaussian_centered_flux
    hd hP hβ ha t ⟨0, by omega⟩ s hs
  constructor
  · intro t
    simpa only [transposeEndpoint, heq] using hflux t
  · simpa [transposeEndpoint, heq] using hflux 0

end EinsteinFull.Blueprint
