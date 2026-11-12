import EinsteinRelation.Environment.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Mul

/-! # Pointwise algebra of the scalar corrected function

Source `paper/main.tex:1053-1069`, Steps 3 and 4 of Proposition 6.1 (`scalar.decomposition`).

For a direction `j`, the local corrector `φ_j` and its skew-symmetric field `Σ_j` satisfy the
flux equation `a (e_j + Dφ_j) = ā e_j + Div Σ_j + F_j`, where the `l`-th entry of `Div Σ_j` is the
weak divergence of the `l`-th row of `Σ_j`. The corrected function `v = u + ∑_j φ_j D_j u` has
gradient `Dv = Du + ∑_j (D_j u Dφ_j + φ_j D D_j u)`.

This file proves the pointwise algebra behind the weak identities of Steps 3 and 4: the corrected
flux identity for `a Dv`, its first-row form, and the skew contraction that cancels the
double-divergence terms. The weak horizontal calculus is not part of this file.
-/

open scoped BigOperators Matrix

namespace EinsteinRelation.Correctors

variable {d : ℕ}

/-- Skew contraction. For a skew-symmetric `S` and a symmetric `H`, the entrywise pairing
`∑ l, ∑ k, S l k * H l k` vanishes. In Step 3 the matrix `H` collects second horizontal derivatives
`D_k D_l F` of a test function, which are symmetric in `(k, l)`, so the skew corrector drops out of
the double divergence `D·((Div Σ) D_j u) = -D·(Σ D D_j u)`. -/
theorem scalarCorrected_skew_sum_eq_zero (S H : Mat d) (hS : S.transpose = -S)
    (hH : H.transpose = H) : ∑ l, ∑ k, S l k * H l k = 0 := by
  have hSk : ∀ l k, S k l = -S l k := fun l k => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hS l) k
  have hHk : ∀ l k, H k l = H l k := fun l k => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun hH l) k
  have hswap : ∑ l, ∑ k, S l k * H l k = ∑ l, ∑ k, S k l * H k l := Finset.sum_comm
  have hneg : ∑ l, ∑ k, S k l * H k l = -∑ l, ∑ k, S l k * H l k := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hSk l k, hHk l k]
    ring
  linarith

/-- For a symmetric matrix `a`, the pairing of `a e_i` with `x` is the `i`-th entry of `a x`. -/
theorem scalarCorrected_dot_mulVec_unitVector (a : Mat d) (ha : a.transpose = a) (i : Fin d)
    (x : Vec d) : dot (a *ᵥ unitVector i) x = (a *ᵥ x) i := by
  have hcol : ∀ k, (a *ᵥ unitVector i) k = a k i := fun k => by
    simp [unitVector, Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite]
  have hsym : ∀ k, a k i = a i k := fun k => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun ha i) k
  show ∑ k, (a *ᵥ unitVector i) k * x k = ∑ k, a i k * x k
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hcol k, hsym k]

/-- Coordinate expansion of a vector in the unit basis. -/
theorem scalarCorrected_eq_sum_unitVector (x : Vec d) : x = ∑ j, x j • unitVector j := by
  funext k
  simp [unitVector, Pi.single_apply, mul_ite]

/-- Matrix action in the unit basis: `M x = ∑_j x_j M e_j`. -/
theorem scalarCorrected_mulVec_eq_sum (M : Mat d) (x : Vec d) :
    M *ᵥ x = ∑ j, x j • (M *ᵥ unitVector j) := by
  conv_lhs => rw [scalarCorrected_eq_sum_unitVector x]
  rw [Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul]

/-- Corrected flux identity (`paper/main.tex:1053-1054`). Let `a` be the coefficient, `ā` the
homogenized matrix and `Du` the gradient of `u`. The local flux equation at direction `j` reads
`a (e_j + Dφ_j) = ā e_j + (R_j + F_j)`, where `R_j` is the divergence of the `j`-th skew corrector.
For the corrected gradient `Dv = Du + ∑_j (D_j u Dφ_j + φ_j D D_j u)`,
`a Dv = ā Du + ∑_j D_j u (R_j + F_j) + ∑_j φ_j a D D_j u`. -/
theorem scalarCorrected_mulVec_gradient (a abar : Mat d) (Du : Vec d) (phi : Fin d → ℝ)
    (Dphi DDu R F : Fin d → Vec d)
    (hflux : ∀ j : Fin d, a *ᵥ (unitVector j + Dphi j) = abar *ᵥ unitVector j + (R j + F j)) :
    a *ᵥ (Du + ∑ j, (Du j • Dphi j + phi j • DDu j)) =
      abar *ᵥ Du + ∑ j, Du j • (R j + F j) + ∑ j, phi j • (a *ᵥ DDu j) := by
  have hj : ∀ j : Fin d, Du j • (a *ᵥ Dphi j) =
      Du j • (abar *ᵥ unitVector j) + Du j • (R j + F j) - Du j • (a *ᵥ unitVector j) := by
    intro j
    have h := hflux j
    rw [Matrix.mulVec_add] at h
    have hD : a *ᵥ Dphi j = abar *ᵥ unitVector j + (R j + F j) - a *ᵥ unitVector j := by
      rw [← h]
      abel
    simp only [hD, smul_sub, smul_add]
  have hsplit : ∀ j : Fin d, a *ᵥ (Du j • Dphi j + phi j • DDu j) =
      Du j • (a *ᵥ Dphi j) + phi j • (a *ᵥ DDu j) := fun j => by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul]
  rw [Matrix.mulVec_add, Matrix.mulVec_sum]
  simp only [hsplit, hj, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← scalarCorrected_mulVec_eq_sum a Du, ← scalarCorrected_mulVec_eq_sum abar Du]
  abel

/-- First-row form of the corrected flux identity (`paper/main.tex:1060-1069`). Let `a` and `ā` be
symmetric, and let `Sig j` be the `j`-th skew corrector. For a row index `i`, the pairing
`a e_i · Dv` splits as
`a e_i · Dv - h = ā e_i · Du + ∑_j (D_j u R_{j,i} + (Sig_j D D_j u)_i)`,
where `h = ∑_j (φ_j a e_i · D D_j u - (Sig_j D D_j u)_i + D_j u F_{j,i})`.
The entry `(Sig_j *ᵥ D D_j u) i` is the pairing of the `i`-th row of `Sig_j` with `D D_j u`. -/
theorem scalarCorrected_dot_first_row (a abar : Mat d) (ha : a.transpose = a)
    (hab : abar.transpose = abar) (Du : Vec d) (phi : Fin d → ℝ) (Dphi DDu R F : Fin d → Vec d)
    (Sig : Fin d → Mat d)
    (hflux : ∀ j : Fin d, a *ᵥ (unitVector j + Dphi j) = abar *ᵥ unitVector j + (R j + F j))
    (i : Fin d) :
    dot (a *ᵥ unitVector i) (Du + ∑ j, (Du j • Dphi j + phi j • DDu j)) -
        ∑ j, (phi j * dot (a *ᵥ unitVector i) (DDu j) - (Sig j *ᵥ DDu j) i + Du j * F j i) =
      dot (abar *ᵥ unitVector i) Du + ∑ j, (Du j * R j i + (Sig j *ᵥ DDu j) i) := by
  have hv := scalarCorrected_mulVec_gradient a abar Du phi Dphi DDu R F hflux
  simp only [scalarCorrected_dot_mulVec_unitVector a ha i,
    scalarCorrected_dot_mulVec_unitVector abar hab i]
  rw [hv]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, mul_add,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

end EinsteinRelation.Correctors
