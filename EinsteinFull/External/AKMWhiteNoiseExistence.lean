import EinsteinFull.External.Draft.AKMWhiteNoiseExistence

namespace EinsteinFull.External

/-- Reviewed Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Proposition 5.14 (printed p. 201), with Definition 5.1 and Remark 5.15: for every
dimension `d ≥ 2` there is a unit scalar white-noise law on distributions, observed through
compact smooth test evaluations. Direct-PDF evidence: literature-akm-white-noise-v1. The
environment built from it, its smoothness, stationarity, finite range and the sharpness argument
stay internal. -/
axiom akm_white_noise_exists : EinsteinFull.External.Draft.akmWhiteNoiseExistenceStmt

end EinsteinFull.External
