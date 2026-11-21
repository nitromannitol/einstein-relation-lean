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

/-! Vocabulary for `EinsteinFull.External.AKMWhiteNoiseExistence`. That library module proves
`EinsteinFull.External.akm_white_noise_exists` as a theorem, so the challenge statements and the
permitted axioms use none of its declarations; the file keeps the import structure of the
challenges. -/
