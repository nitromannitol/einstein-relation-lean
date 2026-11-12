import EinsteinRelation.Correctors.CanonicalSkewLocalRegularity
import EinsteinRelation.Correctors.SkewRegularRepresentativeSelection

/-! Source: `paper/main.tex:741-753,762-766`. A jointly measurable
heat-selected skew family admits a jointly measurable continuous version
with precisely the same source identities and selected stationary gradient. -/

open MeasureTheory
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM External.GilbargTrudinger HeatSelectedSkewMeaning

/-- GT regularity and measurable averaging regularize any jointly
measurable canonical heat-selected skew family, retaining its volume class. -/
theorem exists_continuous_heatSelectedSkewCorrector_representative
    (h68 : FluxGradientEstimate) (hP : BallPoincareEstimate)
    (h836 : InteriorRegularRepresentative)
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ} (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (σ : FieldPair d → Vec d → Mat d)
    (hσ : HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ)
    (hm : Measurable (fun p : Vec d × FieldPair d => σ p.2 p.1)) :
    ∃ σ' : FieldPair d → Vec d → Mat d,
      HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ' ∧
      Measurable (fun p : Vec d × FieldPair d => σ' p.2 p.1) ∧
      (∀ᵐ ω ∂reducedEnvironmentLaw Q, Continuous (σ' ω)) ∧
      ∀ᵐ ω ∂reducedEnvironmentLaw Q, σ ω =ᵐ[volume] σ' ω := by
  obtain ⟨hs, hc, he⟩ := skewRegularRepresentative_preserves_heatSelectedSkewCorrector
    (Fact.out : 2 ≤ d) Q i σ hσ
    (ae_heatSelectedSkewCorrector_continuousOn_representatives h68 hP h836 Q i σ hσ)
  exact ⟨skewRegularRepresentative σ, hs, measurable_skewRegularRepresentative σ hm, hc, he⟩

end EinsteinRelation.Correctors
