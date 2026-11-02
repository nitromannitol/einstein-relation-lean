import Mathlib.Analysis.Distribution.Distribution
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Draft.AKMWhiteNoiseExistence
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.WhiteNoise
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Sharpness.NoiseKernel

/-! Vocabulary for `EinsteinFull.External.AKMWhiteNoiseExistence`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinFull.External

/-- Reviewed Armstrong–Kuusi–Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Proposition 5.14 (printed p. 201), with Definition 5.1 and Remark 5.15: for every
dimension `d ≥ 2` there is a unit scalar white-noise law on distributions, observed through
compact smooth test evaluations. Direct-PDF evidence: literature-akm-white-noise-v1. The
environment built from it, its smoothness, stationarity, finite range and the sharpness argument
stay internal. -/
axiom akm_white_noise_exists : EinsteinFull.External.Draft.akmWhiteNoiseExistenceStmt

end EinsteinFull.External
