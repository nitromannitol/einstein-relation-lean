import EinsteinRelation.Correctors.P53SourceSkewColumn
import EinsteinRelation.Correctors.HeatSelectedSkewGaugeUniqueness
import EinsteinRelation.Correctors.CenteredGaugeMeasurability

/-! Source: `paper/main.tex:770-786,886-894`. Centered point observables
of any continuous heat-selected skew corrector are a.e. measurable.
The jointly measurable potential is constructed from the cited flux
estimate; no measurability of the supplied representative is assumed. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger NormalizedSpatialRepresentativeSupport
open HeatSelectedSkewMeaning

/-- The heat-selected source predicate and a.e. continuity suffice for
measurability of the literal centered skew observable. The measurable
gauge is constructed in this development; its uniqueness is proved modulo constants.
Source: `paper/main.tex:770-786,886-894`. -/
theorem aestronglyMeasurable_conditionalCenteredSkew_of_continuous
    (h68 : FluxGradientEstimate) (hP : BallPoincareEstimate)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀)
    (ζ : SourceMollifier d) (R : ℝ) (hR : 1 ≤ R) (y : Point d) (i : Fin d)
    (σ : FieldPair d → Vec d → Mat d)
    (hσ : HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ)
    (hc : ∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (σ ω)) :
    AEStronglyMeasurable (conditionalCenteredSkew ζ R y σ) (reducedEnvironmentLaw Q) := by
  obtain ⟨τ, hτ, hτm, -, -⟩ := exists_heatSelectedSkewCorrectorColumn h68 hP Q i
  exact aestronglyMeasurable_centered_skew_of_measurable_gauge
    (reducedEnvironmentLaw Q) ζ R hR y σ τ hτm hc
    (ae_heatSelectedSkew_potentials_differ_by_constants Q i τ σ hτ hσ)

end EinsteinRelation.Correctors
