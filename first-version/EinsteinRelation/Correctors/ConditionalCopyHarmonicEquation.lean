import EinsteinRelation.Correctors.CanonicalHarmonicFromPoincare
import EinsteinRelation.Correctors.CorrectorConditionalStatement
import EinsteinRelation.Correctors.PairedCorrectorEquation
import EinsteinRelation.Correctors.SpatialWeakLocalization

/-! # Harmonicity of the actual conditional copies

Source: `paper/main.tex:852–860,878–886`. The variational flux equation
and the normalized scalar weak-gradient equation hold under both actual
copy marginals. Coefficient agreement then makes their difference harmonic
on the entire observed open set. No independence or pointwise regularity
of the prescribed representatives is needed for these weak identities.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open NormalizedScalarPhysicalLawTransportSupport NormalizedSpatialRepresentativeSupport

attribute [local instance] ReductionImageV3.fieldPair_standardBorel

local instance copyHarmonicRestrictionMeasurableSpace {d : ℕ} (U : Set (Vec d)) :
    MeasurableSpace C(U, Mat d) := borel C(U, Mat d)

/-- The actual canonical coefficient flux is samplewise divergence-free.
Source: `paper/main.tex:852–860`. -/
theorem ae_conditionalCorrectorGradient_flux_divergence
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q, HasWeakDivergence Set.univ
      (fun x => (ω.1 x).mulVec
        (unitVector i + conditionalCorrectorGradient Q i (WithLp.toLp 2 x) ω))
      (fun _ => 0) := by
  filter_upwards [ae_canonicalCorrectorFlux_hasWeakDivergence Q i,
    ae_spatial_canonicalCorrectorFlux Q i measurable_id] with ω hdiv hflux
  exact (HasWeakDivergence.restrict_subset (Set.subset_univ _) MeasurableSet.univ hdiv).congr_ae
    (ae_restrict_of_ae hflux) (ae_eq_refl _)

/-- Actual normalized scalar copies have a harmonic difference on any
observed open set. The conclusion concerns the literal production gradient
and scalar carriers. Source: `paper/main.tex:852–860,878–886`. -/
theorem ae_reducedConditionalCopy_scalar_harmonic
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d)
    (φ : FieldPair d → Point d → ℝ)
    (hφ : IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ)
    (U : Set (Vec d)) (hU : IsOpen U) :
    ∀ᵐ z ∂reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U,
      HasWeakGradient U
        (fun x => φ z.2.1 (WithLp.toLp 2 x) - φ z.2.2 (WithLp.toLp 2 x))
        (fun x => conditionalCorrectorGradient Q i (WithLp.toLp 2 x) z.2.1 -
          conditionalCorrectorGradient Q i (WithLp.toLp 2 x) z.2.2) ∧
      HasWeakDivergence U
        (fun x => (z.2.1.1 x).mulVec
          (conditionalCorrectorGradient Q i (WithLp.toLp 2 x) z.2.1 -
            conditionalCorrectorGradient Q i (WithLp.toLp 2 x) z.2.2))
        (fun _ => 0) := by
  obtain ⟨_, hfirst, hsecond, hagree⟩ :=
    reducedConditionalCopy_properties (reducedEnvironmentLaw Q) U hU
  have hmp₁ : MeasurePreserving
      (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) => z.2.1)
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U)
      (reducedEnvironmentLaw Q) := ⟨measurable_fst.comp measurable_snd, hfirst⟩
  have hmp₂ : MeasurePreserving
      (fun z : C(U, Mat d) × (FieldPair d × FieldPair d) => z.2.2)
      (reducedConditionalCopyLaw (reducedEnvironmentLaw Q) U)
      (reducedEnvironmentLaw Q) := ⟨measurable_snd.comp measurable_snd, hsecond⟩
  filter_upwards [hagree, hmp₁.quasiMeasurePreserving.ae hφ.2,
    hmp₂.quasiMeasurePreserving.ae hφ.2,
    hmp₁.quasiMeasurePreserving.ae (ae_conditionalCorrectorGradient_flux_divergence Q i),
    hmp₂.quasiMeasurePreserving.ae (ae_conditionalCorrectorGradient_flux_divergence Q i)]
    with z hz hφ₁ hφ₂ hd₁ hd₂
  obtain ⟨_, hg₁, _⟩ := hφ₁
  obtain ⟨_, hg₂, _⟩ := hφ₂
  exact paired_corrector_harmonic hU hz (unitVector i)
    (hasWeakGradient_mono (Set.subset_univ _) hg₁)
    (hasWeakGradient_mono (Set.subset_univ _) hg₂)
    (hasWeakDivergence_mono (Set.subset_univ _) hd₁)
    (hasWeakDivergence_mono (Set.subset_univ _) hd₂)

end EinsteinRelation.Correctors
