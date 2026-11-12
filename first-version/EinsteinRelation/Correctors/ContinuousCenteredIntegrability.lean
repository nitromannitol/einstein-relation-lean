import EinsteinRelation.Correctors.PlanarCenteredIntegrability
import EinsteinRelation.Correctors.ContinuousSkewCenteredMeasurability

/-! Source: `paper/main.tex:872-894`. The single-field affine comparison
and stationary L² gradient give integrability of the actual continuous
centered observables without joint measurability of the supplied skew field. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport
local instance integrablePlanarFact : Fact (2 ≤ 2) := ⟨le_rfl⟩

/-- The joint amplitude domination argument is invariant under an a.e.
replacement of the matrix observable. Source: `paper/main.tex:886-894`. -/
theorem integrable_scalar_and_entries_of_joint_bound_ae
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    {d : ℕ} (f : Ω → ℝ) (S : Ω → Mat d) (E : Ω → ℝ)
    (hf : Measurable f) (hS : AEStronglyMeasurable S μ) (hE : Integrable E μ)
    (c : ℝ) (A : Mat d)
    (hb : ∀ᵐ ω ∂μ, |f ω-c| + frobeniusNorm (S ω-A) ≤ E ω) :
    Integrable f μ ∧ ∀ i j, Integrable (fun ω => S ω i j) μ := by
  letI : TopologicalSpace.PseudoMetrizableSpace (Mat d) :=
    inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace (Fin d → Fin d → ℝ))
  have hb' : ∀ᵐ ω ∂μ, |f ω-c| + frobeniusNorm (hS.mk S ω-A) ≤ E ω := by
    filter_upwards [hb, hS.ae_eq_mk] with ω hω heq
    rw [← heq]
    exact hω
  obtain ⟨hfi, hSi⟩ := integrable_scalar_and_entries_of_joint_bound μ f (hS.mk S) E
    hf hS.measurable_mk hE c A hb'
  refine ⟨hfi, fun i j => (hSi i j).congr ?_⟩
  exact hS.ae_eq_mk.symm.mono fun _ h => congrFun (congrFun h i) j

/-- The continuous Lemma 5.2 representatives have integrable centered
scalar and skew entries under the actual reduced environment law.
Source: `paper/main.tex:872-894`. -/
theorem integrable_planar_centered_correctors_of_continuous
    (h68 : FluxGradientEstimate) (h817 : LocalBoundednessEstimate) (hP : BallPoincareEstimate)
    {L r₀ : ℝ} (Q : EnvironmentLaw 2 L r₀)
    (ζ : SourceMollifier 2) (R : ℝ) (hR : 1 ≤ R) (y : Point 2) (i : Fin 2)
    (φ : FieldPair 2 → Point 2 → ℝ) (σ : FieldPair 2 → Vec 2 → Mat 2)
    (hφ : IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ)
    (hσ : HasHeatSelectedSkewCorrectorColumn (by decide) Q i σ)
    (hc : ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) ∧ Continuous (σ ω)) :
    Integrable (conditionalCenteredScalar ζ R y φ) (reducedEnvironmentLaw Q) ∧
      ∀ a b, Integrable (fun ω => conditionalCenteredSkew ζ R y σ ω a b)
        (reducedEnvironmentLaw Q) := by
  obtain ⟨C, -, hb⟩ := ae_single_planar_centered_correctors_le_affine_energy
    h817 hP L planar_affine_reference_equations
  have hmφ := (measurable_conditionalCentered_of_joint ζ R y φ
    (fun _ _ => 0) hφ.1 (fun _ _ => measurable_const)).1
  have hmσ := aestronglyMeasurable_conditionalCenteredSkew_of_continuous
    h68 hP Q ζ R hR y i σ hσ (hc.mono fun _ h => h.2)
  have hi := (integrable_canonicalTotalGradientRms Q i y (2*R) (by linarith)).const_mul (C*R)
  exact integrable_scalar_and_entries_of_joint_bound_ae (reducedEnvironmentLaw Q)
    _ _ _ hmφ hmσ hi _ _ (hb Q ζ R hR y i φ σ hφ hσ hc)

end EinsteinRelation.Correctors
