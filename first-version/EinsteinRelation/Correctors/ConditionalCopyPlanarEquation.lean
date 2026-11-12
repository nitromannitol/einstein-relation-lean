import EinsteinRelation.Correctors.HeatSelectedSkewRowEquation
import EinsteinRelation.Correctors.PlanarSkewAlmostEverywhere
import EinsteinRelation.Correctors.PairedPDEPlanarEquation
import EinsteinRelation.Correctors.GTRegularCoefficientSupport

/-! # The planar equation on the actual conditional-copy law

Source: `paper/main.tex:869–886`. Actual scalar copies provide the ordinary
weak gradient; heat-selected skew copies provide the row-divergence.
Almost-everywhere skewness suffices for the independent entry's gradient.
The dual ellipticity follows from the original environment law.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open NormalizedScalarPhysicalLawTransportSupport NormalizedSpatialRepresentativeSupport
open HeatSelectedSkewMeaning

attribute [local instance] ReductionImageV3.fieldPair_standardBorel
local instance planarDimensionFact : Fact (2 ≤ 2) := ⟨by decide⟩
local instance planarCopyRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- Global ellipticity, including all spatial points simultaneously, for
the actual reduced law. Source: `paper/main.tex:196–207,869–872`. -/
theorem ae_reducedEnvironmentLaw_field_isElliptic
    {d : ℕ} {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, IsElliptic (sourceReducedBound L) ω.1 := by
  filter_upwards [ActualImageLpStateTransport.ae_reducedEnvironmentLaw_mem_image Q]
    with ω hω
  obtain ⟨η, hη, rfl⟩ := hω
  exact (sourceReducedBound_support Q.ellipticity_parameter hη).2.1

/-- Both components of the dual harmonic equation hold for the actual
production conditional copies, with no extra PDE or skewness assumptions.
This weak statement does not assert pointwise representative regularity.
Source: `paper/main.tex:869–886`. -/
theorem ae_reducedConditionalCopy_planar_harmonic
    {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀) (i : Fin 2)
    (ζ : SourceMollifier 2) (R : ℝ) (hR : 1 ≤ R) (y : Point 2)
    (φ : FieldPair 2 → Point 2 → ℝ)
    (σ : FieldPair 2 → Vec 2 → Mat 2)
    (hφ : IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ)
    (hσ : HasHeatSelectedSkewCorrectorColumn (by norm_num) Q i σ)
    (U : Set (Vec 2)) (hU : IsOpen U) :
    ∀ᵐ z ∂reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U,
      HasWeakGradient U (fun x => σ z.2.1 x 0 1 - σ z.2.2 x 0 1)
        (fun x => planarRotation.mulVec ((z.2.1.1 x).mulVec
          (conditionalCorrectorGradient Q i (WithLp.toLp 2 x) z.2.1 -
            conditionalCorrectorGradient Q i (WithLp.toLp 2 x) z.2.2))) ∧
      HasWeakDivergence U
        (fun x => (planarRotation * (z.2.1.1 x)⁻¹ * planarRotation.transpose).mulVec
          (planarRotation.mulVec ((z.2.1.1 x).mulVec
            (conditionalCorrectorGradient Q i (WithLp.toLp 2 x) z.2.1 -
              conditionalCorrectorGradient Q i (WithLp.toLp 2 x) z.2.2))))
        (fun _ => 0) := by
  obtain ⟨_, hfirst, hsecond, hagree⟩ :=
    reducedConditionalCopy_properties (reducedEnvironmentLaw Q) U hU
  have hmp₁ : MeasurePreserving
      (fun z : C(U, Mat 2) × (FieldPair 2 × FieldPair 2) => z.2.1)
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U)
      (reducedEnvironmentLaw Q) := ⟨measurable_fst.comp measurable_snd, hfirst⟩
  have hmp₂ : MeasurePreserving
      (fun z : C(U, Mat 2) × (FieldPair 2 × FieldPair 2) => z.2.2)
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U)
      (reducedEnvironmentLaw Q) := ⟨measurable_snd.comp measurable_snd, hsecond⟩
  have hskew : ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      ∀ᵐ x ∂volume, (σ ω x).transpose = -(σ ω x) :=
    hσ.choose_spec.2.mono fun _ h => h.1.1
  have hL : 0 < sourceReducedBound L := by
    unfold sourceReducedBound
    exact mul_pos (Real.exp_pos _) (by nlinarith [sq_nonneg L, Q.ellipticity_parameter])
  filter_upwards [hagree,
    ae_reducedConditionalCopy_scalar_harmonic Q i ζ R hR y φ hφ U hU,
    hmp₁.quasiMeasurePreserving.ae (ae_heatSelectedSkew_rowDivergence Q i σ hσ),
    hmp₂.quasiMeasurePreserving.ae (ae_heatSelectedSkew_rowDivergence Q i σ hσ),
    hmp₁.quasiMeasurePreserving.ae hskew, hmp₂.quasiMeasurePreserving.ae hskew,
    hmp₁.quasiMeasurePreserving.ae (ae_reducedEnvironmentLaw_field_isElliptic Q)]
    with z hz hscalar hrow₁ hrow₂ hs₁ hs₂ hell
  have hrow := paired_fluxCorrector_rowDivergence hU hz (unitVector i)
    (expectedCorrectorFlux Q i).ofLp
    (fun j => hasWeakDivergence_mono (Set.subset_univ _) (hrow₁ j))
    (fun j => hasWeakDivergence_mono (Set.subset_univ _) (hrow₂ j))
  have hs : ∀ᵐ x ∂volume.restrict U,
      (σ z.2.1 x - σ z.2.2 x).transpose = -(σ z.2.1 x - σ z.2.2 x) := by
    filter_upwards [ae_restrict_of_ae hs₁, ae_restrict_of_ae hs₂] with x hx₁ hx₂
    rw [Matrix.transpose_sub, hx₁, hx₂]
    abel
  constructor
  · simpa only [Matrix.sub_apply, planarRotation_mulVec] using
      hasWeakGradient_planar_skew_entry_of_ae hU
        (fun x => σ z.2.1 x - σ z.2.2 x) _ hs hrow
  · exact planar_dual_harmonic_of_weakGradient hU hL hell hscalar.1 (fun _ _ => rfl)

end EinsteinRelation.Correctors
