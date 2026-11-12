import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Function.L2Space
import EinsteinRelationAudit.SharpExample.Vocabulary.Calculus.Weak
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.EllipticOperatorBound
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Basic
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Bounds
import EinsteinRelationAudit.SharpExample.Vocabulary.Environment.Reduction

/-! Restated from the library module `EinsteinRelation.Calculus.WeightedFormIntegrabilitySupport`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

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
