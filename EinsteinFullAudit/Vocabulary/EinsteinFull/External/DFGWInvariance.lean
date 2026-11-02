import Mathlib.Probability.Kernel.Basic
import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic
import Mathlib.Topology.CompactOpen
import Mathlib.Order.Hom.Basic
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
import EinsteinFullAudit.Vocabulary.EinsteinFull.External.Draft.DFGWInvarianceV2
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Diffusion.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction

/-! Vocabulary for `EinsteinFull.External.DFGWInvariance`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

namespace EinsteinFull.External

/-- Reviewed De Masi–Ferrari–Goldstein–Wick (1989), Theorem 2.2 with Remarks 1 and 3, on the
continuous trajectory space, part (ii) in the Skorokhod space. Direct-PDF evidence:
literature-dfgw-invariance-v3 (after v1 and v2). The application to the environment seen from
the particle, the transport to the two-sided carrier and the continuous-path corollary stay
internal. -/
axiom dfgw_invariance : EinsteinFull.External.Draft.dfgwInvarianceStmtV2

end EinsteinFull.External
