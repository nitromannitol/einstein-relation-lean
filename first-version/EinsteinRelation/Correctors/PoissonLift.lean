import EinsteinRelation.External.GilbargTrudinger

/-!
# A scalar lift of an inhomogeneous Poisson equation

Source: `paper/main.tex:735-739`. Adding a height coordinate permits a
bounded divergence source to be encoded in a symmetric elliptic matrix.
The source is divided by a bound before applying homogeneous local
boundedness. This file defines the explicit spatial objects only.
-/
namespace EinsteinRelation.Correctors

/-- The original coordinates, following the added height coordinate. -/
def poissonLiftBase {d : ℕ} (x : Vec (d + 1)) : Vec d := fun i => x i.succ

/-- A symmetric matrix with quadratic form `s² + |ξ - s F|²`. -/
def poissonLiftMatrix {d : ℕ} (F : Vec d) : Mat (d + 1) :=
  fun i j => Fin.cases
    (Fin.cases (1 + euclideanSq F) (fun k => -F k) j)
    (fun k => Fin.cases (-F k) (fun l => if k = l then 1 else 0) j) i

/-- The lifted scalar potential, linear in the added coordinate. -/
def poissonLiftPotential {d : ℕ} (u : Vec d → ℝ) (M : ℝ) (x : Vec (d + 1)) : ℝ :=
  u (poissonLiftBase x) + M * x 0

/-- The explicit gradient of the lifted potential. -/
def poissonLiftGradient {d : ℕ} (g : Vec d → Vec d) (M : ℝ)
    (x : Vec (d + 1)) : Vec (d + 1) :=
  Fin.cons M (g (poissonLiftBase x))

/-- A lifted flux with height-independent components. -/
def poissonLiftFlux {d : ℕ} (F : Vec d → Vec d) (B : Vec d → ℝ)
    (x : Vec (d + 1)) : Vec (d + 1) :=
  Fin.cons (B (poissonLiftBase x)) (F (poissonLiftBase x))

/-- The matrix action separates the height component from the original flux. -/
theorem poissonLiftMatrix_mulVec {d : ℕ} (F : Vec d) (ξ : Vec (d + 1)) :
    (poissonLiftMatrix F).mulVec ξ =
      Fin.cons ((1 + euclideanSq F) * ξ 0 - dot F (poissonLiftBase ξ))
        (fun i => ξ i.succ - F i * ξ 0) := by
  ext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, poissonLiftMatrix,
      poissonLiftBase, dot, neg_mul, Finset.sum_neg_distrib, sub_eq_add_neg]
  · simp [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, poissonLiftMatrix,
      neg_mul, sub_eq_add_neg, add_comm]

/-- After normalization by `M`, the original components are exactly `g - F`. -/
theorem poissonLiftMatrix_normalized_flux {d : ℕ} (F g : Vec d) (M : ℝ)
    (hM : M ≠ 0) :
    (poissonLiftMatrix (M⁻¹ • F)).mulVec (Fin.cons M g) =
      Fin.cons ((1 + euclideanSq (M⁻¹ • F)) * M - dot (M⁻¹ • F) g) (g - F) := by
  rw [poissonLiftMatrix_mulVec]
  congr 1
  funext i
  simp [Pi.smul_apply, smul_eq_mul, mul_comm, hM]

end EinsteinRelation.Correctors
