import EinsteinRelation.Correctors.ReducedConditionalCopies
import EinsteinRelation.Correctors.ConditionalCopyEuclideanJensen
import EinsteinRelation.Correctors.StationarySpatialRealizationSupport

/-! # Conditional Jensen for the actual canonical gradient

Source: `paper/main.tex:886–894`. Stationarity supplies integrability of
the canonical gradient at every prescribed point. Conditional Jensen
therefore applies to its actual spatial realization on the reduced law,
with the coefficient restriction as observation.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open StationarySpatialRealization

attribute [local instance] ReductionImageV3.fieldPair_standardBorel

/-- The literal canonical gradient at a prescribed point is square
integrable under the actual reduced environment law.
Source: `paper/main.tex:770–772,886–894`. -/
theorem memLp_canonicalGradient_slice {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (y : Vec d) :
    MemLp (fun ω => spatialRealization (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) (y, ω))
      2 (reducedEnvironmentLaw Q) :=
  (Lp.memLp (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))).comp_measurePreserving
      (measurePreserving_translate _ (reducedEnvironmentLaw_stationary Q) y)

/-- Conditional-copy Jensen for the actual canonical gradient at every
prescribed point. The observation is exactly the production coefficient
sigma algebra; no integrability premise is imposed on the gradient.
Source: `paper/main.tex:770–772,886–894`. -/
theorem eLpNorm_canonicalGradient_conditional_error_le_copy_difference
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (y : Vec d) (U : Set (Vec d)) (hU : IsOpen U)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    letI : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)
    let μ := reducedEnvironmentLaw Q
    let X := reducedCoefficientRestriction U
    let grad : FieldPair d → EuclideanSpace ℝ (Fin d) := fun ω =>
      spatialRealization (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 μ) (y, ω)
    eLpNorm (grad - μ[grad | Carriers.reducedCoefficientObservationSigma U]) p μ ≤
      eLpNorm (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) =>
        grad z.2.1 - grad z.2.2) p
        ((μ.map X) ⊗ₘ (condDistrib (id : FieldPair d → FieldPair d) X μ ×ₖ
          condDistrib (id : FieldPair d → FieldPair d) X μ)) := by
  letI : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)
  dsimp only
  rw [reducedCoefficientObservationSigma_eq_comap_restriction U hU]
  apply eLpNorm_conditional_error_piL2_le_copy_difference (Fin d)
    (reducedEnvironmentLaw Q) (reducedCoefficientRestriction U)
    (measurable_reducedCoefficientRestriction U) hp hpt
  · exact (measurable_spatialRealization _).comp
      (measurable_const.prodMk measurable_id)
  · exact (memLp_canonicalGradient_slice Q i y).integrable one_le_two

end EinsteinRelation.Correctors
