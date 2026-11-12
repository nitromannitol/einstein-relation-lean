import EinsteinRelation.Correctors.P53SourceSkewColumn
import EinsteinRelation.Correctors.CanonicalSkewRegularRepresentative
import EinsteinRelation.Correctors.CanonicalScalarRegularExistence

/-! Source: `paper/main.tex:694-708,735-753,762-766`. The actual canonical
scalar and heat-selected skew correctors have jointly measurable versions
that are continuous in space on one full-measure event. The skew witness is
chosen once, before the scalar normalization radius and center. -/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning
open NormalizedSpatialRepresentativeSupport NormalizedScalarPhysicalLawTransportSupport

/-- A jointly measurable continuous heat-selected skew corrector exists,
conditional only on the existing AKM, Poincaré, and GT inputs. -/
theorem exists_continuous_heatSelectedSkewCorrectorColumn
    (h68 : FluxGradientEstimate) (hP : BallPoincareEstimate)
    (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d) :
    ∃ σ : FieldPair d → Vec d → Mat d,
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ ∧
      Measurable (fun p : Vec d × FieldPair d => σ p.2 p.1) ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (σ ω) := by
  obtain ⟨σ, hσ, hm, -, -⟩ := exists_heatSelectedSkewCorrectorColumn h68 hP Q i
  have hm' : Measurable (fun p : Vec d × FieldPair d => σ p.2 p.1) := by
    change @Measurable _ (Fin d → Fin d → ℝ) _ (borel _) _
    rw [← (Pi.borelSpace (X := fun _ : Fin d => Fin d → ℝ)).measurable_eq]
    exact measurable_pi_lambda _ (fun j => measurable_pi_lambda _
      (fun k => (hm j k).comp measurable_swap))
  obtain ⟨σ', hs, hms, hc, -⟩ :=
    exists_continuous_heatSelectedSkewCorrector_representative h68 hP h836 Q i σ hσ hm'
  exact ⟨σ', hs, hms, hc⟩

/-- Regular corrector existence with a common skew family for every scalar
mollifier normalization. Both correctors are continuous almost surely,
as required for evaluation in the conditional corrector bound. -/
theorem exists_continuousCanonicalCorrectors
    (h68 : FluxGradientEstimate) (hP : BallPoincareEstimate)
    (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (ζ : SourceMollifier d) (i : Fin d) :
    ∃ σ : FieldPair d → Vec d → Mat d,
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ ∧
      Measurable (fun p : Vec d × FieldPair d => σ p.2 p.1) ∧
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (σ ω)) ∧
      ∀ (R : ℝ) (hR : 1 ≤ R) (y : Point d),
        ∃ φ : FieldPair d → Point d → ℝ,
          IsNormalizedCanonicalScalarCorrector Q i ζ R hR y φ ∧
          ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (φ ω) ∧ Continuous (σ ω) := by
  obtain ⟨σ, hσ, hm, hc⟩ := exists_continuous_heatSelectedSkewCorrectorColumn h68 hP h836 Q i
  refine ⟨σ, hσ, hm, hc, fun R hR y => ?_⟩
  obtain ⟨φ, hφ, hφc⟩ := exists_continuous_normalizedCanonicalScalarCorrector hP h836 Q i ζ R hR y
  exact ⟨φ, hφ, by filter_upwards [hφc, hc] with ω hωφ hωσ using ⟨hωφ, hωσ⟩⟩

end EinsteinRelation.Correctors
