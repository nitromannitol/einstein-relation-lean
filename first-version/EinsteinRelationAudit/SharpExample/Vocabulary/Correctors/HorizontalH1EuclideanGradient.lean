import EinsteinRelationAudit.SharpExample.Vocabulary.Calculus.HorizontalSobolev
import EinsteinRelationAudit.SharpExample.Vocabulary.Correctors.EuclideanLpCoordinateAssembly

/-! Restated from the library module `EinsteinRelation.Correctors.HorizontalH1EuclideanGradient`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open MeasureTheory
namespace EinsteinRelation.Correctors
/-- Source main.tex240-248 and 694-707: for `f` in the horizontal H¹ domain, there is an `L²(Q)`
function with values in the Euclidean space `ℝ^d` whose coordinates are the horizontal derivatives
`D_i f` almost everywhere, and whose squared Euclidean `L²` norm is `∑ i, ‖D_i f‖²`. -/
theorem exists_euclidean_horizontalH1Gradient {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (f : horizontalH1 Q hQ) :
    ∃ g : Lp (EuclideanSpace ℝ (Fin d)) 2 Q,
      (∀ i : Fin d, (fun ω => g ω i) =ᵐ[Q] (horizontalH1Gradient Q hQ f i : FieldPair d → ℝ)) ∧
      ‖g‖^2 = ∑ i : Fin d, ‖horizontalH1Gradient Q hQ f i‖^2 :=
  exists_Lp_euclidean_of_coordinates Q (horizontalH1Gradient Q hQ f)
end EinsteinRelation.Correctors
