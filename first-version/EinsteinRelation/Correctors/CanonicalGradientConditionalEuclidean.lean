import EinsteinRelation.Correctors.CanonicalGradientConditionalCopies
import EinsteinRelation.TimeChange.EuclideanTransport

/-! The literal Euclidean norm and coordinate conditional expectation in
`paper/main.tex:770–772,886–894`. Continuous linear transport commutes with
conditional expectation, so the Hilbert-space copy estimate has exactly
the source's coordinate expression, with no dimension factor. -/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open StationarySpatialRealization

attribute [local instance] ReductionImageV3.fieldPair_standardBorel

/-- Coordinate transport preserves the conditional-error Euclidean seminorm.
Source: `paper/main.tex:770–772`. -/
theorem eLpNorm_euclidean_conditional_error_eq_piL2
    {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (m : MeasurableSpace Ω) {f : Ω → EuclideanSpace ℝ (Fin d)}
    (hf : Integrable f μ) (p : ℝ≥0∞) :
    eLpNorm (fun ω => euclideanNorm ((f ω).ofLp -
      condExp m μ (fun ω' => (f ω').ofLp) ω)) p μ =
      eLpNorm (f - condExp m μ f) p μ := by
  let T : EuclideanSpace ℝ (Fin d) →L[ℝ] Vec d :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℝ)).toContinuousLinearMap
  have hc := T.comp_condExp_comm (m := m) hf
  calc
    _ = eLpNorm (fun ω => ‖f ω - condExp m μ f ω‖) p μ := by
      apply eLpNorm_congr_ae
      filter_upwards [hc] with ω hω
      change T (condExp m μ f ω) = condExp m μ (fun ω' => T (f ω')) ω at hω
      change euclideanNorm (T (f ω) - condExp m μ (fun ω' => T (f ω')) ω) = _
      rw [← hω, ← map_sub, TimeChange.euclideanNorm_eq_norm_toLp]
      rfl
    _ = _ := eLpNorm_norm _

/-- Conditional-copy Jensen for the source's actual canonical gradient,
using the literal coordinate conditional mean and Euclidean norms on both
sides. Source: `paper/main.tex:770–772,886–894`. -/
theorem eLpNorm_canonicalGradient_euclidean_conditional_error_le_copy_difference
    {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (y : Vec d) (U : Set (Vec d)) (hU : IsOpen U)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hpt : p ≠ ∞) :
    letI : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)
    let μ := reducedEnvironmentLaw Q
    let X := reducedCoefficientRestriction U
    let grad : FieldPair d → Vec d := fun ω =>
      (spatialRealization (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 μ) (y, ω)).ofLp
    eLpNorm (fun ω => euclideanNorm
      (grad ω - condExp (Carriers.reducedCoefficientObservationSigma U) μ grad ω)) p μ ≤
      eLpNorm (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) =>
        euclideanNorm (grad z.2.1 - grad z.2.2)) p
        ((μ.map X) ⊗ₘ (condDistrib (id : FieldPair d → FieldPair d) X μ ×ₖ
          condDistrib (id : FieldPair d → FieldPair d) X μ)) := by
  letI : MeasurableSpace C(U, Mat d) := borel C(U, Mat d)
  dsimp only
  rw [eLpNorm_euclidean_conditional_error_eq_piL2 _ _
    ((memLp_canonicalGradient_slice Q i y).integrable one_le_two)]
  refine (eLpNorm_canonicalGradient_conditional_error_le_copy_difference
    Q i y U hU hp hpt).trans_eq ?_
  rw [← eLpNorm_norm]
  apply eLpNorm_congr_ae
  filter_upwards [] with z
  rw [TimeChange.euclideanNorm_eq_norm_toLp]
  rfl

end EinsteinRelation.Correctors
