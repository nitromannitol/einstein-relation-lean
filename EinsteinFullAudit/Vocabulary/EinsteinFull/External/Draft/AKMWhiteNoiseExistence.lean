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
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.External.WhiteNoise
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Sharpness.NoiseKernel

/-! Vocabulary for `EinsteinFull.External.Draft.AKMWhiteNoiseExistence`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinFull.External.Draft

/-- AKM Proposition 5.14, restricted to real compact smooth tests and
    transported to the evaluation sigma-algebra on distributions. -/
def akmWhiteNoiseExistenceStmt : Prop :=
  ∀ d : ℕ, 2 ≤ d → EinsteinRelation.External.WhiteNoiseExistence d

end EinsteinFull.External.Draft
