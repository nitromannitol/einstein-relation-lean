import EinsteinRelation.Correctors.EuclideanLpCoordinateAssembly
import EinsteinRelation.Calculus.HorizontalSobolev

/-! # Euclidean-valued horizontal H¹ gradient in `L²`

Source anchors: paper/main.tex:240-248 (the space `H¹(Q)` of `f ∈ L²(Q)` with `D_j f ∈ L²(Q)` for all `j`,
and the horizontal derivative `D = (D_1, …, D_d)`), and paper/main.tex:688-701 (the corrector estimates,
where the gradients are measured in the Euclidean norm).

For `f` in the actual horizontal H¹ domain `horizontalH1 Q hQ`, the coordinate derivatives
`horizontalH1Gradient Q hQ f i` are assembled into one `L²(Q)` function with values in
`EuclideanSpace ℝ (Fin d)`. Its `i`-th coordinate is the `i`-th derivative almost everywhere, and its
squared Euclidean `L²` norm is the sum of the squared coordinate norms. This consumes the coordinate
assembly `exists_Lp_euclidean_of_coordinates` directly. No probability measure, no pointwise gradient
hypothesis, and no maximum-norm replacement is used.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Source main.tex240-248 and 688-701: for `f` in the horizontal H¹ domain, there is an `L²(Q)`
function with values in the Euclidean space `ℝ^d` whose coordinates are the horizontal derivatives
`D_i f` almost everywhere, and whose squared Euclidean `L²` norm is `∑ i, ‖D_i f‖²`. -/
theorem exists_euclidean_horizontalH1Gradient {d : ℕ} (Q : Measure (FieldPair d))
    (hQ : IsStationary Q) (f : horizontalH1 Q hQ) :
    ∃ g : Lp (EuclideanSpace ℝ (Fin d)) 2 Q,
      (∀ i : Fin d, (fun ω => g ω i) =ᵐ[Q] (horizontalH1Gradient Q hQ f i : FieldPair d → ℝ)) ∧
      ‖g‖^2 = ∑ i : Fin d, ‖horizontalH1Gradient Q hQ f i‖^2 :=
  exists_Lp_euclidean_of_coordinates Q (horizontalH1Gradient Q hQ f)

end EinsteinRelation.Correctors
