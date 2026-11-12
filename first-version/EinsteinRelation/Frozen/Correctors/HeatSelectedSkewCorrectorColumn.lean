import EinsteinRelation.Correctors.HeatSelectedSkewMeaningSupport

namespace EinsteinRelation.Correctors

/-- The source skew-corrector column with its stationary gradient selected by
    the iterated AKM heat formula for the canonical centered flux. -/
def HasHeatSelectedSkewCorrectorColumn {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d)
    (σ : FieldPair d → Vec d → Mat d) : Prop :=
  HeatSelectedSkewMeaning.HasHeatSelectedSkewCorrectorColumn hd Q i σ

end EinsteinRelation.Correctors
