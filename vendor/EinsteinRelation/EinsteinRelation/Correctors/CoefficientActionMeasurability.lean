import EinsteinRelation.Correctors.CoefficientProjectionSymmetricAction

/-!
# The actual coefficient action respects coefficient observations

Source: `paper/main.tex:693-698`. The actual origin matrix and its action
on a coefficient-measurable vector are measurable with respect to the
coefficient observations alone. Symmetry then gives projection commutation.
-/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors

/-- The actual origin matrix action preserves coefficient-only measurability. -/
theorem reducedOriginCoefficientAction_aestronglyMeasurable_coefficients
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
    (hG : AEStronglyMeasurable[coefficientObservations d] G (reducedEnvironmentLaw Q)) :
    AEStronglyMeasurable[coefficientObservations d]
      (reducedOriginCoefficientAction Q G) (reducedEnvironmentLaw Q) := by
  have : TopologicalSpace.PseudoMetrizableSpace (Mat d) := by
    change TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ)
    infer_instance
  have : SecondCountableTopology (Mat d) := by
    change SecondCountableTopology (Fin d → Fin d → ℝ)
    infer_instance
  let A : Mat d × EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    fun p => WithLp.toLp 2 (p.1.mulVec p.2.ofLp)
  have hc : Continuous A :=
    (PiLp.continuous_toLp (p := 2) (β := fun _ : Fin d => ℝ)).comp
      (continuous_fst.matrix_mulVec
        ((PiLp.continuous_ofLp (p := 2) (β := fun _ : Fin d => ℝ)).comp continuous_snd))
  have hm : Measurable[coefficientObservations d]
      (fun ω : FieldPair d => ω.1 (0 : Vec d)) :=
    (continuous_eval_const (0 : Vec d)).measurable.comp (comap_measurable Prod.fst)
  have h := hc.comp_aestronglyMeasurable (hm.aestronglyMeasurable.prodMk hG)
  apply h.congr
  filter_upwards [reducedOriginCoefficientAction_coeFn Q G] with ω hω
  exact (congrArg (WithLp.toLp 2) hω).symm

/-- The coefficient projection commutes with the actual origin coefficient
operator, with no extra operator-invariance premise. -/
theorem coefficientProjection_reducedOriginCoefficientAction
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (G : Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q)) :
    coefficientProjection (reducedEnvironmentLaw Q) (EuclideanSpace ℝ (Fin d))
      (reducedOriginCoefficientAction Q G) =
    reducedOriginCoefficientAction Q
      (coefficientProjection (reducedEnvironmentLaw Q) (EuclideanSpace ℝ (Fin d)) G) :=
  coefficientProjection_commutes_of_symmetric (reducedEnvironmentLaw Q)
    (reducedOriginCoefficientAction Q) (reducedOriginCoefficientAction_symmetric Q)
    (reducedOriginCoefficientAction_aestronglyMeasurable_coefficients Q) G

end EinsteinRelation.Correctors
