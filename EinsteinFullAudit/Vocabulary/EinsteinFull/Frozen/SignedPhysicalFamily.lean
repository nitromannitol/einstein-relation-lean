import Mathlib.Probability.Martingale.Basic
import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Kernel.Composition.MapComap
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Diffusion.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction

/-! Vocabulary for `EinsteinFull.Frozen.SignedPhysicalFamily`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

namespace EinsteinFull

open EinsteinRelation

/-- The physical diffusion of Section 1 for every real force, specified by its
conservative martingale problem at the origin. -/
def IsSignedPhysicalFamily {d : ℕ} {Λ₀ r₀ : ℝ} (i : Fin d)
    (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d) : Prop :=
  ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
    SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (P lam (0, ω))

end EinsteinFull
