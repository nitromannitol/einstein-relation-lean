import EinsteinRelation.Correctors.AKMCanonicalColumnPositiveTimeMoments
import EinsteinRelation.Correctors.CoupledScalarMomentAverage
import EinsteinRelation.Correctors.PhysicalCouplingLift

/-! # The paired scalar profile of the same canonical column flow

Source: `paper/main.tex:850–855`. The initial layer is derived from the
actual coefficient regularity, and the only remaining scalar estimate is
the large-time bound on the supplied flow. Arbitrary probability spatial
averages and all couplings with the actual marginals share the constant.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport ReductionImageV3

/-- The actual paired scalar RMS has the complete shifted decay profile.
This needs no independence or scalar initial-bound hypothesis. All moments
refer to the same supplied canonical flow. Source: `paper/main.tex:850–855`. -/
theorem physicalCoupling_canonical_column_coupled_profile
    (d : ℕ) (L r₀ C : ℝ) (hC : 0 ≤ C) :
    ∃ M : ℝ, 0 < M ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
      (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => u z.1 z.2) →
      (∀ᵐ A ∂actualCoefficientLaw Q,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
      ∀ p : ℝ, 2 ≤ p →
      (∀ t : ℝ, 1 ≤ t → ∀ x : Vec d,
        eLpNorm (fun A => u A (t,x)) (ENNReal.ofReal p) (actualCoefficientLaw Q) ≤
          ENNReal.ofReal (C*t^(-(1 : ℝ)/2-(d : ℝ)/4))) →
      ∀ μ : Measure (PhysicalField d L × PhysicalField d L), IsProbabilityMeasure μ →
      MeasurePreserving Prod.fst μ (physicalReferenceLaw Q) →
      MeasurePreserving Prod.snd μ (physicalReferenceLaw Q) →
      ∀ ν : Measure (Vec d), IsProbabilityMeasure ν →
      Measurable (fun z : ℝ × (PhysicalField d L × PhysicalField d L) =>
        Real.sqrt (∫ x, (u (project (r₀ := r₀) Q.ellipticity_parameter z.2.1) (z.1,x) - u (project (r₀ := r₀) Q.ellipticity_parameter z.2.2) (z.1,x))^2 ∂ν)) ∧
      ∀ t : ℝ, 0 < t →
        (∀ᵐ A ∂μ, MemLp (fun x => u (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - u (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x)) 2 ν) ∧
        MemLp (fun A => Real.sqrt (∫ x, (u (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - u (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x))^2 ∂ν))
          (ENNReal.ofReal p) μ ∧
        eLpNorm (fun A => Real.sqrt (∫ x, (u (project (r₀ := r₀) Q.ellipticity_parameter A.1) (t,x) - u (project (r₀ := r₀) Q.ellipticity_parameter A.2) (t,x))^2 ∂ν))
          (ENNReal.ofReal p) μ ≤
          ENNReal.ofReal (M*(1+t)^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
  obtain ⟨M, hM, hprofile⟩ :=
    actualCoefficientLaw_canonical_column_positive_time_moments d L r₀ C hC
  refine ⟨2*M, mul_pos two_pos hM, ?_⟩
  intro Q i u G hum hflow p hp hlate μ hμ hfst hsnd ν hν
  letI : IsProbabilityMeasure (physicalReferenceLaw Q) := physicalReferenceLaw_probability Q
  letI : IsProbabilityMeasure μ := hμ
  letI : IsProbabilityMeasure ν := hν
  generalize hπdef : project (d := d) (r₀ := r₀) Q.ellipticity_parameter = π
  have hπ : MeasurePreserving π (physicalReferenceLaw Q) (actualCoefficientLaw Q) :=
    hπdef ▸ measurePreserving_akmProject Q
  have hvm : Measurable (fun z : PhysicalField d L × (ℝ × Vec d) => u (π z.1) z.2) :=
    hum.comp (hπ.measurable.prodMap measurable_id)
  have hpair : Measurable (fun q : (ℝ × (PhysicalField d L × PhysicalField d L)) ×
      Vec d => (u (π q.1.2.1) (q.1.1,q.2) - u (π q.1.2.2) (q.1.1,q.2))^2) :=
    ((hvm.comp (measurable_fst.snd.fst.prodMk
      (measurable_fst.fst.prodMk measurable_snd))).sub
      (hvm.comp (measurable_fst.snd.snd.prodMk
        (measurable_fst.fst.prodMk measurable_snd)))).pow_const 2
  refine ⟨hpair.stronglyMeasurable.integral_prod_right'.measurable.sqrt, ?_⟩
  intro t ht
  have hpoint (x : Vec d) := hprofile Q i u G hum hflow p hp hlate t ht x
  have hpoint' (x : Vec d) :
      MemLp (fun ω => u (π ω) (t,x)) (ENNReal.ofReal p) (physicalReferenceLaw Q) ∧
      eLpNorm (fun ω => u (π ω) (t,x)) (ENNReal.ofReal p) (physicalReferenceLaw Q) ≤
        ENNReal.ofReal (M*(1+t)^(-(1 : ℝ)/2-(d : ℝ)/4)) := by
    refine ⟨(hpoint x).1.comp_measurePreserving hπ, ?_⟩
    exact (eLpNorm_comp_measurePreserving
      (hpoint x).1.aestronglyMeasurable hπ).trans_le (hpoint x).2
  have htime : Measurable (fun q : PhysicalField d L × Vec d =>
      u (π q.1) (t,q.2)) :=
    hvm.comp (show Measurable (fun q : PhysicalField d L × Vec d => (q.1,(t,q.2))) from
      measurable_fst.prodMk (measurable_const.prodMk measurable_snd))
  have h := coupled_scalarL2_average_moment_le (physicalReferenceLaw Q) μ hfst hsnd ν
    hp (mul_nonneg hM.le (Real.rpow_nonneg (by linarith) _))
    (fun q => u (π q.1) (t,q.2))
    htime hpoint'
  simpa only [mul_assoc] using h

end EinsteinRelation.Correctors
