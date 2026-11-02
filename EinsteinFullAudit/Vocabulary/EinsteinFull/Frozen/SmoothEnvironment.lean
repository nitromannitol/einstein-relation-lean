import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.EnvironmentLaw
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.SmoothWithBounds
import EinsteinFullAudit.Vocabulary.EinsteinFull.Frozen.StructuralData
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Smooth

/-! Vocabulary for `EinsteinFull.Frozen.SmoothEnvironment`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

namespace EinsteinFull

/-- Assumption 1.2 on the environment law, with all derivative orders on one
almost-sure event and the fixed deterministic bounds of the structural data. -/
def HasSmoothBounds {d : ℕ} (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) : Prop :=
  ∀ᵐ ω ∂Q.measure, IsSmoothWithBounds D.derivativeBound ω

end EinsteinFull
