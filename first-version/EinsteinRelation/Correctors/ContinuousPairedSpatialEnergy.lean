import EinsteinRelation.Correctors.CanonicalPairedSpatialEnergy
import EinsteinRelation.Correctors.ContinuousCanonicalGradient

/-! # Spatial energy transport to the continuous canonical gradient

Source: `paper/main.tex:852–867`. The selected continuous version agrees
with the stationary gradient almost everywhere after the actual physical
dilation. Spatial energies therefore retain their sharp coupled rate.
-/

open MeasureTheory Set
open scoped ENNReal
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger Environment.AKMTestIntegralSupport ReductionImageV3
open NormalizedSpatialRepresentativeSupport

/-- Physical dilation preserves the spatial volume-class identity of the
continuous canonical gradient. Source: `paper/main.tex:852–867`. -/
theorem ae_physical_continuous_gradient_dilation
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂physicalReferenceLaw Q,
      (fun x => continuousCanonicalGradient Q i (reduce ω.1) (r₀ • x)) =ᵐ[volume]
        fun x => ((canonicalCorrectorGradient Q i :
          Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
            (translate (r₀ • x) (reduce ω.1))).ofLp := by
  filter_upwards [(measurePreserving_physicalReduction Q).quasiMeasurePreserving.ae
    (ae_continuousCanonicalGradient hP h836 Q i)] with ω hω
  exact (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (zero_lt_one.trans_le Q.range_parameter).ne').ae hω.2

/-- The continuous canonical gradient has the sharp paired spatial RMS
bound under the actual physical coupling. Point values are fixed by the
already constructed continuous version, not selected from spatial a.e.
identities. Source: `paper/main.tex:852–867`. -/
theorem continuous_canonical_gradient_paired_spatial_decay
    (hdecay : ParabolicSemigroupKernelDecay) (hreg : ParabolicLargeScale)
    (hP : BallPoincareEstimate) (h836 : InteriorRegularRepresentative)
    (d : ℕ) [Fact (2 ≤ d)] (L r₀ m : ℝ) (hL : 1 ≤ L) (hm : 2 ≤ m) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : EnvironmentLaw d L r₀) (i : Fin d)
      (u : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → ℝ)
      (G : Coefficient d (AKMUpperEllipticity L) → ℝ × Vec d → Vec d),
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => u z.1 z.2) →
      Measurable (fun z : Coefficient d (AKMUpperEllipticity L) ×
        (ℝ × Vec d) => G z.1 z.2) →
      (∀ᵐ A ∂actualCoefficientLaw Q,
        IsSemigroupSolution A (fun x => (A x).mulVec (unitVector i)) (u A) (G A) ∧
        HasCanonicalKernelRepresentation A (fun x => (A x).mulVec (unitVector i)) (u A)) →
      (∀ᵐ A ∂actualCoefficientLaw Q, ∀ t : ℝ, 0 < t →
        HasWeakGradient univ (fun x => u A (t,x)) (fun x => G A (t,x))) →
      ∀ R : ℝ, 1 ≤ R → ∀ y : Point d,
      let F := fun z : PhysicalField d L × PhysicalField d L =>
        vectorRms volume (originBall d (2*R)) (fun x =>
          continuousCanonicalGradient Q i (reduce z.1.1) (r₀ • x) -
          continuousCanonicalGradient Q i (reduce z.2.1) (r₀ • x))
      MemLp F (ENNReal.ofReal m) (recenteredPhysicalCopyLaw Q (r₀*R) y) ∧
      eLpNorm F (ENNReal.ofReal m) (recenteredPhysicalCopyLaw Q (r₀*R) y) ≤
        ENNReal.ofReal (C*R^(-(d : ℝ)/2)) := by
  obtain ⟨C,hC,hbound⟩ := canonical_gradient_paired_spatial_decay
    hdecay hreg d Fact.out L r₀ m hL hm
  refine ⟨C,hC,?_⟩
  intro Q i u G hu hG hflow hweak R hR y
  dsimp only
  have hb := hbound Q i u G hu hG hflow hweak R hR y
  obtain ⟨_,_,hfst,hsnd,_⟩ := recenteredPhysicalCopy_properties Q (r₀*R) y
  let ν : Measure (Vec d) :=
    (volume (originBall d (2*R)))⁻¹ • volume.restrict (originBall d (2*R))
  have hν : ν ≪ volume :=
    Measure.smul_absolutelyContinuous.trans Measure.restrict_le_self.absolutelyContinuous
  have heq : (fun z : PhysicalField d L × PhysicalField d L =>
      vectorRms volume (originBall d (2*R)) (fun x =>
        continuousCanonicalGradient Q i (reduce z.1.1) (r₀ • x) -
        continuousCanonicalGradient Q i (reduce z.2.1) (r₀ • x))) =ᵐ[recenteredPhysicalCopyLaw Q (r₀*R) y]
      fun z => Real.sqrt (∫ x, ‖(canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • x) (reduce z.1.1)) -
        (canonicalCorrectorGradient Q i :
        Lp (EuclideanSpace ℝ (Fin d)) 2 (reducedEnvironmentLaw Q))
          (translate (r₀ • x) (reduce z.2.1))‖^2 ∂ν) := by
    have hid := ae_physical_continuous_gradient_dilation hP h836 Q i
    filter_upwards [hfst.quasiMeasurePreserving.ae hid,hsnd.quasiMeasurePreserving.ae hid]
      with z h₁ h₂
    unfold vectorRms
    rw [setAverage_eq']
    congr 1
    apply integral_congr_ae
    filter_upwards [h₁.filter_mono hν.ae_le,h₂.filter_mono hν.ae_le] with x hx₁ hx₂
    rw [hx₁,hx₂]
    rw [← Real.sq_sqrt (euclideanSq_nonneg_fisher _)]
    change (euclideanNorm _)^2 = _
    rw [TimeChange.euclideanNorm_eq_norm_toLp]
    rfl
  exact ⟨(memLp_congr_ae heq).mpr hb.2.1,(eLpNorm_congr_ae heq).trans_le hb.2.2⟩

end EinsteinRelation.Correctors
