import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Topology.Metrizable.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Topology.ContinuousMap.Algebra
import Mathlib.Topology.Instances.Matrix
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Probability.Independence.Basic
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Calculus.FDeriv.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Generator
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Calculus.Weak
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Basic
import EinsteinFullAudit.Vocabulary.EinsteinRelation.Environment.Reduction

/-! Vocabulary for `EinsteinRelation.Calculus.WeightedFormIntegrabilitySupport`: the declarations of that library module which the challenge statements use, copied verbatim in their context. -/

open MeasureTheory

open scoped InnerProductSpace

namespace EinsteinRelation.SpatialDirichlet

noncomputable section

/-- A representative and its distributional weak gradient, both in weighted `L²`. -/
structure WeightedSobolevGraph {d : ℕ} (m : Measure (Vec d)) where
  value : Vec d → ℝ
  weakGradient : Vec d → EuclideanSpace ℝ (Fin d)
  value_memLp : MemLp value 2 m
  gradient_memLp : MemLp weakGradient 2 m
  distributionalGradient : HasWeakGradient Set.univ value
    (fun x => WithLp.ofLp (weakGradient x))

/-- The literal Euclidean bilinear energy integrand for a coefficient field. -/
def weightedFormIntegrand {d : ℕ} {m : Measure (Vec d)} (A : Vec d → Mat d)
    (u v : WeightedSobolevGraph m) : Vec d → ℝ := fun x => (1 / 2 : ℝ) *
      dot (WithLp.ofLp (u.weakGradient x))
        ((A x).mulVec (WithLp.ofLp (v.weakGradient x)))

end

end EinsteinRelation.SpatialDirichlet
