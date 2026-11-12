import EinsteinRelation.Correctors.CorrectorConditionalStatement
import EinsteinRelation.Correctors.CoupledDifferenceMoments

/-! # Higher canonical-gradient moments on the actual copy law

Source: `paper/main.tex:859–862,878–886`. The bad-event gradient moment
comes from the original marginal moments, with no independence premise.
-/

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open NormalizedSpatialRepresentativeSupport StationarySpatialRealization

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance momentRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Stationarity transfers every finite moment of the canonical gradient
to every prescribed spatial point. Source: `paper/main.tex:859–862,886`. -/
theorem eLpNorm_canonicalGradient_slice_eq_origin {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (y : Point d) (p : ℝ≥0∞) :
    eLpNorm (fun ω => euclideanNorm (conditionalCorrectorGradient Q i y ω)) p
        (reducedEnvironmentLaw Q) =
      eLpNorm (fun ω => euclideanNorm (conditionalCorrectorGradient Q i 0 ω)) p
        (reducedEnvironmentLaw Q) := by
  let f := (canonicalCorrectorGradient Q i :
    Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
  have heq (z : Point d) : (fun ω => euclideanNorm (conditionalCorrectorGradient Q i z ω)) =
      fun ω => ‖f (translate (WithLp.ofLp z) ω)‖ := by
    funext ω
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
    rfl
  rw [heq y, heq 0]
  simp only [WithLp.ofLp_zero, translate_zero]
  exact eLpNorm_comp_measurePreserving (Lp.aestronglyMeasurable f).norm
    (measurePreserving_translate _ (reducedEnvironmentLaw_stationary Q) (WithLp.ofLp y))

/-- Higher moments of the actual copy difference are bounded by twice the
single-field moment. This discharges the bad-radius paired-gradient moment
from Lemma 5.1. Source: `paper/main.tex:859–862,878–886`. -/
theorem canonicalGradientCopy_moment_le {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (y : Point d)
    (U : Set (Vec d)) (hU : IsOpen U) {p : ℝ≥0∞} (hp : 1 ≤ p)
    {B : ℝ} (hB : 0 ≤ B)
    (hbound : eLpNorm (fun ω => euclideanNorm (conditionalCorrectorGradient Q i 0 ω)) p
      (reducedEnvironmentLaw Q) ≤ ENNReal.ofReal B) :
    let Z := fun z : C(U, Mat d) × (FieldPair d × FieldPair d) =>
      euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
        conditionalCorrectorGradient Q i y z.2.2)
    MemLp Z p (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U) ∧
      eLpNorm Z p (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U) ≤
        ENNReal.ofReal (2 * B) := by
  let μ := reducedEnvironmentLaw Q
  let P := reducedConditionalCopyLaw μ U
  let f : FieldPair d → EuclideanSpace ℝ (Fin d) := fun ω =>
    spatialRealization (canonicalCorrectorGradient Q i :
      Lp (EuclideanSpace ℝ (Fin d)) 2 μ) (WithLp.ofLp y, ω)
  have hfb : eLpNorm f p μ ≤ ENNReal.ofReal B := by
    have hy := (eLpNorm_canonicalGradient_slice_eq_origin Q i y p).trans_le hbound
    simpa only [conditionalCorrectorGradient, TimeChange.euclideanNorm_eq_norm_toLp,
      WithLp.toLp_ofLp, eLpNorm_norm] using hy
  have hf : MemLp f p μ := ⟨(memLp_canonicalGradient_slice Q i (WithLp.ofLp y)).1,
    hfb.trans_lt ENNReal.ofReal_lt_top⟩
  obtain ⟨_, h₁, h₂, _⟩ := reducedConditionalCopy_properties μ U hU
  have hfirst : MeasurePreserving
      (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) => z.2.1) P μ :=
    ⟨measurable_fst.comp measurable_snd, h₁⟩
  have hsecond : MeasurePreserving
      (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) => z.2.2) P μ :=
    ⟨measurable_snd.comp measurable_snd, h₂⟩
  have heq (z : C(U, Mat d) × (FieldPair d × FieldPair d)) :
      euclideanNorm (conditionalCorrectorGradient Q i y z.2.1 -
        conditionalCorrectorGradient Q i y z.2.2) = ‖f z.2.1 - f z.2.2‖ := by
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
    rfl
  dsimp only
  simp_rw [heq]
  exact coupledDifference_moment_le hfirst hsecond hp hf.1 hB hfb


end EinsteinRelation.Correctors
