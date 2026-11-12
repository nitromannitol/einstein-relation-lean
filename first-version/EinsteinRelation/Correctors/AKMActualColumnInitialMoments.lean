import EinsteinRelation.Correctors.AKMActualPairedEnergyTrace

/-! # Initial-layer moments on the actual normalized law

Source: `paper/main.tex:850–852`. Bounded weak divergence of physical
coefficient columns gives all stochastic moments of a specified canonical
flow, uniformly through its initial time layer.
-/

open MeasureTheory
open scoped ENNReal
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport

/-- Every probability moment, including the essential supremum, of the
specified canonical flow has the actual deterministic initial-data bound.
Source: `paper/main.tex:850–852`. -/
theorem actualCoefficientLaw_canonical_column_moments
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
    (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d)
    (hum : Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
      (ℝ × Vec d) => u z.1 z.2))
    (hflow : ∀ᵐ A ∂actualCoefficientLaw Q,
      IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
      HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A))
    (p : ℝ≥0∞) (t : ℝ) (ht : 0 < t) (x : Vec d) :
    MemLp (fun A => u A (t,x)) p (actualCoefficientLaw Q) ∧
      eLpNorm (fun A => u A (t,x)) p (actualCoefficientLaw Q) ≤
        ENNReal.ofReal ((d : ℝ) * akmColumnLipschitzConstant d L r₀) := by
  letI : IsProbabilityMeasure (actualCoefficientLaw Q) := actualCoefficientLaw_probability Q
  have hm : AEStronglyMeasurable (fun A => u A (t,x)) (actualCoefficientLaw Q) :=
    (hum.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable
  have hb : ∀ᵐ A ∂actualCoefficientLaw Q,
      ‖u A (t,x)‖ ≤ (d : ℝ) * akmColumnLipschitzConstant d L r₀ := by
    filter_upwards [ae_actualCoefficientLaw_canonical_column_bound Q i u G hflow] with A hA
    simpa only [Real.norm_eq_abs] using hA t ht x
  refine ⟨MemLp.of_bound hm _ hb, ?_⟩
  simpa only [measure_univ, ENNReal.one_rpow, one_mul] using eLpNorm_le_of_ae_bound (p := p) hb

end EinsteinRelation.Correctors
