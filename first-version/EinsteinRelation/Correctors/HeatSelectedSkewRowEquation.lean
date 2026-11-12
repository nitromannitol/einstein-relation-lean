import EinsteinRelation.Correctors.CanonicalFluxPoissonData
import EinsteinRelation.Correctors.ConditionalCopyHarmonicEquation

/-! # The literal row equation for heat-selected skew correctors

Source: `paper/main.tex:688–702,869–872`. The source testing identity
is converted into the production weak row-divergence predicate, keeping
its actual scalar representatives and the canonical coefficient flux.
-/

open MeasureTheory
namespace EinsteinRelation.Correctors
open HeatSelectedSkewMeaning

/-- A heat-selected column has its source row equation with all local
integrability obligations discharged. Source: `paper/main.tex:688–702`. -/
theorem ae_heatSelectedSkew_rowDivergence
    {d : ℕ} [Fact (2 ≤ d)] {L r₀ : ℝ}
    (Q : EnvironmentLaw d L r₀) (i : Fin d)
    (σ : FieldPair d → Vec d → Mat d)
    (hσ : HasHeatSelectedSkewCorrectorColumn (Fact.out : 2 ≤ d) Q i σ) :
    ∀ᵐ ω ∂reducedEnvironmentLaw Q,
      HasWeakRowDivergence Set.univ (σ ω)
        (fun x => (ω.1 x).mulVec
          (unitVector i + conditionalCorrectorGradient Q i (WithLp.toLp 2 x) ω) -
          (expectedCorrectorFlux Q i).ofLp) := by
  obtain ⟨F, _, hF⟩ := hσ
  filter_upwards [hF, ae_canonicalCenteredFlux_locallyIntegrable Q i,
    ae_spatial_canonicalCorrectorFlux Q i measurable_id] with ω hω hloc hflux
  have hrow : HasWeakRowDivergence Set.univ (σ ω)
      (fun x => (canonicalCorrectorFlux Q i (translate x ω) -
        expectedCorrectorFlux Q i).ofLp) := by
    intro j
    refine ⟨fun k => (hω.2.2 j k j).1, (hloc j).locallyIntegrableOn _, ?_⟩
    intro ψ hψ
    have heq := (hω.1.2.1 ψ hψ.1 hψ.2.1 j).2.2
    simpa only [neg_neg, Measure.restrict_univ, dot, gradient] using
      (congrArg Neg.neg heq).symm
  apply hasWeakRowDivergence_congr_ae isOpen_univ hrow (ae_eq_refl _)
  filter_upwards [ae_restrict_of_ae hflux] with x hx
  change (canonicalCorrectorFlux Q i (translate x ω)).ofLp -
    (expectedCorrectorFlux Q i).ofLp = _
  simp only [id_eq] at hx
  rw [hx]
  rfl

end EinsteinRelation.Correctors
