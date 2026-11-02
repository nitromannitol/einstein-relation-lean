import EinsteinRelation.External.WhiteNoise

namespace EinsteinFull.External.Draft

/-- AKM Proposition 5.14, restricted to real compact smooth tests and
    transported to the evaluation sigma-algebra on distributions. -/
def akmWhiteNoiseExistenceStmt : Prop :=
  ∀ d : ℕ, 2 ≤ d → EinsteinRelation.External.WhiteNoiseExistence d

end EinsteinFull.External.Draft
