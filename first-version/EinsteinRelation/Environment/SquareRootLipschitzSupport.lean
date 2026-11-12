import EinsteinRelation.Environment.SquareRootFieldLawSupport

open Matrix
open scoped BigOperators MatrixOrder

namespace EinsteinRelation

private def fsq {d : ℕ} (M : Mat d) : ℝ :=
  ∑ p ∈ Finset.univ.product Finset.univ, (M p.1 p.2) ^ 2

private def fdot {d : ℕ} (M N : Mat d) : ℝ :=
  ∑ p ∈ Finset.univ.product Finset.univ, M p.1 p.2 * N p.1 p.2

private lemma fdot_eq_nested {d : ℕ} (M N : Mat d) :
    fdot M N = ∑ i, ∑ j, M i j * N i j := by
  unfold fdot
  exact Finset.sum_product' Finset.univ Finset.univ (fun i j => M i j * N i j)

private lemma fsq_eq_nested {d : ℕ} (M : Mat d) :
    fsq M = ∑ i, ∑ j, (M i j) ^ 2 := by
  unfold fsq
  exact Finset.sum_product' Finset.univ Finset.univ (fun i j => (M i j) ^ 2)

private lemma root_lower_bound {d : ℕ} {Λ : ℝ} (hΛ : 1 ≤ Λ)
    (A : Mat d) (hA : IsElliptic Λ (fun _ : Vec d => A)) :
    ((Real.sqrt (Λ⁻¹)) • (1 : Mat d)) ≤ CFC.sqrt A := by
  have hH : A.IsHermitian := by
    change Aᴴ = A
    rw [Matrix.conjTranspose_eq_transpose_of_trivial]
    exact (hA 0).1
  let U : Mat d := hH.eigenvectorUnitary
  let c := Real.sqrt (Λ⁻¹)
  let B := hH.cfc Real.sqrt
  have heigLower (i : Fin d) : Λ⁻¹ ≤ hH.eigenvalues i := by
    let v : Vec d := (hH.eigenvectorBasis i).ofLp
    have hvnorm : euclideanSq v = 1 := by
      have hn : ‖hH.eigenvectorBasis i‖ ^ 2 = 1 := by
        rw [hH.eigenvectorBasis.orthonormal.norm_eq_one i]
        norm_num
      have hnorm := (EuclideanSpace.norm_sq_eq (hH.eigenvectorBasis i)).symm.trans hn
      simpa [v, euclideanSq, dot, Real.norm_eq_abs, sq_abs, pow_two] using hnorm
    have hquad := (hA 0).2 v |>.1
    have heq : hH.eigenvalues i = dot v (A.mulVec v) := by
      rw [hH.eigenvalues_eq i]
      simp [v, hH.mulVec_eigenvectorBasis, dot, dotProduct]
    rw [hvnorm, ← heq] at hquad
    simpa using hquad
  have hsqrtEigen (i : Fin d) : 0 ≤ Real.sqrt (hH.eigenvalues i) - c := by
    apply sub_nonneg.mpr
    apply Real.sqrt_le_sqrt
    exact (heigLower i).trans_eq (by simp)
  have hdiag : (diagonal (fun i => Real.sqrt (hH.eigenvalues i) - c)).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    exact hsqrtEigen
  have hBrep : B = U * diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᴴ := by
    change Unitary.conjStarAlgAut ℝ (Mat d) hH.eigenvectorUnitary
      (diagonal (Real.sqrt ∘ hH.eigenvalues)) = _
    rw [Unitary.conjStarAlgAut_apply]
    have hstar : star (↑hH.eigenvectorUnitary : Mat d) =
        (↑hH.eigenvectorUnitary : Mat d)ᴴ := star_eq_conjTranspose _
    rw [hstar]
    rfl
  have hBpsd : B.PosSemidef := by
    rw [hBrep]
    exact (Matrix.PosSemidef.diagonal (fun i => Real.sqrt_nonneg _)).mul_mul_conjTranspose_same U
  have hBsq : B * B = A := by
    rw [hBrep]
    have hArep : A = U * diagonal (hH.eigenvalues) * Uᴴ := by
      simpa [U,
        Matrix.conjTranspose_eq_transpose_of_trivial] using hH.spectral_theorem
    have hU : Uᴴ * U = 1 := by
      change star (↑hH.eigenvectorUnitary : Mat d) *
        (↑hH.eigenvectorUnitary : Mat d) = 1
      exact Unitary.coe_star_mul_self hH.eigenvectorUnitary
    have hdiagSq : diagonal (fun i => Real.sqrt (hH.eigenvalues i)) *
        diagonal (fun i => Real.sqrt (hH.eigenvalues i)) = diagonal (hH.eigenvalues) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      simpa [pow_two] using
        Real.sq_sqrt ((elliptic_matrix_posSemidef hΛ hA 0).eigenvalues_nonneg i)
    have hUcancel : Uᴴ * (U * diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᴴ) =
        diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᴴ := by
      calc
        _ = (Uᴴ * U) * (diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᴴ) := by
          rw [Matrix.mul_assoc, ← Matrix.mul_assoc]
        _ = _ := by rw [hU, one_mul]
    calc
      (U * diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᴴ) *
          (U * diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᴴ) =
          (U * diagonal (fun i => Real.sqrt (hH.eigenvalues i))) *
            (diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᴴ) := by
              calc
                _ = (U * diagonal (fun i => Real.sqrt (hH.eigenvalues i))) *
                    (Uᴴ * (U * diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᴴ)) := by
                      rw [Matrix.mul_assoc]
                _ = (U * diagonal (fun i => Real.sqrt (hH.eigenvalues i))) *
                    (diagonal (fun i => Real.sqrt (hH.eigenvalues i)) * Uᴴ) := by
                      rw [hUcancel]
      _ = U * (diagonal (fun i => Real.sqrt (hH.eigenvalues i)) *
          diagonal (fun i => Real.sqrt (hH.eigenvalues i))) * Uᴴ := by
            simp only [Matrix.mul_assoc]
      _ = U * diagonal (hH.eigenvalues) * Uᴴ := by rw [hdiagSq]
      _ = A := hArep.symm
  have hBroot : CFC.sqrt A = B := CFC.sqrt_unique hBsq hBpsd.nonneg
  have hDiff : (B - c • (1 : Mat d)).PosSemidef := by
    have hconj := hdiag.mul_mul_conjTranspose_same U
    have hU : U * Uᴴ = 1 := by
      change (↑hH.eigenvectorUnitary : Mat d) *
        star (↑hH.eigenvectorUnitary : Mat d) = 1
      exact Unitary.coe_mul_star_self hH.eigenvectorUnitary
    have hUtrans : U * U.transpose = 1 := by
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hU
    have hId : U * (c • (1 : Mat d)) * Uᴴ = c • (1 : Mat d) := by
      calc
        U * (c • (1 : Mat d)) * Uᴴ = c • ((U * 1) * Uᴴ) := by
          rw [Matrix.mul_assoc, Matrix.smul_mul, Matrix.mul_smul]
          congr 1
          rw [← Matrix.mul_assoc]
        _ = c • (1 : Mat d) := by
          rw [Matrix.mul_one, hU]
    have hdiagSub : diagonal (fun i => Real.sqrt (hH.eigenvalues i)) - c • (1 : Mat d) =
        diagonal (fun i => Real.sqrt (hH.eigenvalues i) - c) := by
      ext i j
      by_cases hij : i = j
      · subst j
        simp [diagonal_apply_eq]
      · simp [diagonal_apply_ne _ hij, one_apply_ne hij]
    have hDiffEq : B - c • (1 : Mat d) = U * diagonal (fun i => Real.sqrt (hH.eigenvalues i) - c) * Uᴴ := by
      rw [hBrep]
      rw [← hId]
      rw [← Matrix.sub_mul, ← Matrix.mul_sub]
      rw [hdiagSub]
    rw [hDiffEq]
    exact hconj
  rw [hBroot, Matrix.le_iff]
  simpa [c] using hDiff

private lemma trace_mul_symm {d : ℕ} (D M : Mat d) (hD : D.transpose = D) :
    (D * M).trace = fdot D M := by
  have hsum : (D * M).trace = ∑ i, ∑ j, D i j * M i j := by
    simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have hDij : D j i = D i j := by simpa using congrFun (congrFun hD i) j
    rw [hDij]
  rw [fdot_eq_nested]
  exact hsum

private lemma trace_self_eq_fsq {d : ℕ} (D : Mat d) (hD : D.transpose = D) :
    (D * D).trace = fsq D := by
  rw [trace_mul_symm D D hD, fdot_eq_nested, fsq_eq_nested]
  simp [pow_two]

private lemma trace_mul_psd_nonneg {d : ℕ} (P Q : Mat d)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) : 0 ≤ (P * Q).trace := by
  let R := CFC.sqrt P
  have hR : (R * R = P) := by
    exact CFC.sqrt_mul_sqrt_self P hP.nonneg
  have hRpsd : R.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg P)
  have hRsymm : R.transpose = R := by
    have hHerm : R.IsHermitian := hRpsd.1
    change Rᴴ = R at hHerm
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hHerm
    exact hHerm
  have hconj : (R * Q * R).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hRsymm] using
      hQ.mul_mul_conjTranspose_same R
  have htr : (P * Q).trace = (R * Q * R).trace := by
    rw [← hR, Matrix.mul_assoc, Matrix.trace_mul_comm]
  rw [htr]
  exact hconj.trace_nonneg

private lemma trace_shift_lower {d : ℕ} (c : ℝ) (X D : Mat d)
    (hX : (X - c • (1 : Mat d)).PosSemidef) (hD : (D * D).PosSemidef)
    (hDs : D.transpose = D) : c * fsq D ≤ (X * (D * D)).trace := by
  have hpos := trace_mul_psd_nonneg (X - c • (1 : Mat d)) (D * D) hX hD
  have hsplit : X * (D * D) = (X - c • (1 : Mat d)) * (D * D) + c • (D * D) := by
    rw [sub_mul, Matrix.smul_mul, one_mul]
    module
  rw [hsplit, Matrix.trace_add, Matrix.trace_smul, trace_self_eq_fsq D hDs]
  simp only [smul_eq_mul]
  linarith

private lemma trace_shift_lower_right {d : ℕ} (c : ℝ) (Y D : Mat d)
    (hY : (Y - c • (1 : Mat d)).PosSemidef) (hD : (D * D).PosSemidef)
    (hDs : D.transpose = D) : c * fsq D ≤ ((D * D) * Y).trace := by
  rw [Matrix.trace_mul_comm]
  exact trace_shift_lower c Y D hY hD hDs

/-- The CFC positive square root is Lipschitz in the entrywise Frobenius norm
for real symmetric matrices with a common ellipticity bound. -/
theorem cfcSqrt_frobenius_lipschitz_of_ellipticity {d : ℕ}
    {Λ : ℝ} (hΛ : 1 ≤ Λ) (A B : Mat d)
    (hA : IsElliptic Λ (fun _ : Vec d => A))
    (hB : IsElliptic Λ (fun _ : Vec d => B)) :
    (∑ i, ∑ j, (CFC.sqrt A i j - CFC.sqrt B i j) ^ 2) ≤
      Λ / 4 * (∑ i, ∑ j, (A i j - B i j) ^ 2) := by
  let X := CFC.sqrt A
  let Y := CFC.sqrt B
  let D := X - Y
  let c := Real.sqrt (Λ⁻¹)
  change ∑ i, ∑ j, (D i j) ^ 2 ≤ Λ / 4 * ∑ i, ∑ j, ((A - B) i j) ^ 2
  rw [← fsq_eq_nested D, ← fsq_eq_nested (A - B)]
  have hc : 0 < c := Real.sqrt_pos.mpr (inv_pos.mpr (by linarith))
  have hXs : X.transpose = X := by
    have hs : X.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)
    have hh := hs.1
    change Xᴴ = X at hh
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hh
    exact hh
  have hYs : Y.transpose = Y := by
    have hs : Y.PosSemidef := Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg B)
    have hh := hs.1
    change Yᴴ = Y at hh
    rw [Matrix.conjTranspose_eq_transpose_of_trivial] at hh
    exact hh
  have hDs : D.transpose = D := by simp [D, hXs, hYs]
  have hDpsd : (D * D).PosSemidef := by
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, hDs] using
      Matrix.posSemidef_conjTranspose_mul_self D
  have hXsq : X * X = A := by
    exact CFC.sqrt_mul_sqrt_self A (elliptic_matrix_posSemidef hΛ hA 0).nonneg
  have hYsq : Y * Y = B := by
    exact CFC.sqrt_mul_sqrt_self B (elliptic_matrix_posSemidef hΛ hB 0).nonneg
  have hXlower : c • (1 : Mat d) ≤ X := by
    simpa [c] using root_lower_bound hΛ A hA
  have hYlower : c • (1 : Mat d) ≤ Y := by
    simpa [c] using root_lower_bound hΛ B hB
  have hXlowerP : (X - c • (1 : Mat d)).PosSemidef := Matrix.le_iff.mp hXlower
  have hYlowerP : (Y - c • (1 : Mat d)).PosSemidef := Matrix.le_iff.mp hYlower
  have hSylvester : A - B = X * D + D * Y := by
    change A - B = X * (X - Y) + (X - Y) * Y
    calc
      A - B = X * X - Y * Y := by rw [hXsq, hYsq]
      _ = X * (X - Y) + (X - Y) * Y := by
        rw [Matrix.mul_sub, Matrix.sub_mul]
        abel
  have hpair : fdot D (A - B) = (D * (A - B)).trace := by
    symm
    exact trace_mul_symm D (A - B) hDs
  have hpairLower : 2 * c * fsq D ≤ fdot D (A - B) := by
    rw [hpair, hSylvester, Matrix.mul_add, Matrix.trace_add]
    have hcyc : (D * (X * D)).trace = (X * (D * D)).trace := by
      calc
        (D * (X * D)).trace = (D * (D * X)).trace := by
          simpa [Matrix.mul_assoc] using Matrix.trace_mul_cycle D X D
        _ = (X * (D * D)).trace := by
          calc
            (D * (D * X)).trace = ((D * D) * X).trace := by rw [Matrix.mul_assoc]
            _ = (X * (D * D)).trace := Matrix.trace_mul_comm _ _
    rw [hcyc]
    have hleft := trace_shift_lower c X D hXlowerP hDpsd hDs
    have hright := trace_shift_lower_right c Y D hYlowerP hDpsd hDs
    have hright' : c * fsq D ≤ (D * (D * Y)).trace := by
      simpa [Matrix.mul_assoc] using hright
    linarith
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq
    (Finset.univ.product Finset.univ)
    (fun p : Fin d × Fin d => D p.1 p.2)
    (fun p => (A - B) p.1 p.2)
  have hcs' : (fdot D (A - B)) ^ 2 ≤ fsq D * fsq (A - B) := by
    simpa [fdot, fsq] using hcs
  have hF : 0 ≤ fsq D := by
    unfold fsq
    exact Finset.sum_nonneg fun p hp => sq_nonneg _
  have hF0 : fsq D = 0 ∨ 0 < fsq D := by
    by_cases hz : fsq D = 0
    · exact Or.inl hz
    · exact Or.inr (lt_of_le_of_ne hF (Ne.symm hz))
  rcases hF0 with hF0 | hFpos
  · have hG : 0 ≤ fsq (A - B) := by
      unfold fsq
      exact Finset.sum_nonneg fun p hp => sq_nonneg _
    change fsq D ≤ Λ / 4 * fsq (A - B)
    rw [hF0]
    exact mul_nonneg (by positivity) hG
  · have hlarge : (2 * c * fsq D) ^ 2 ≤ fsq D * fsq (A - B) := by
      calc
        _ ≤ (fdot D (A - B)) ^ 2 := by
          exact (sq_le_sq₀ (by positivity) (le_trans (by positivity) hpairLower)).2
            hpairLower
        _ ≤ fsq D * fsq (A - B) := hcs'
    have hFG : 4 * c ^ 2 * fsq D ≤ fsq (A - B) := by
      apply (le_of_mul_le_mul_of_pos_left ?_ hFpos)
      calc
        fsq D * (4 * c ^ 2 * fsq D) = (2 * c * fsq D) ^ 2 := by ring
        _ ≤ fsq D * fsq (A - B) := by nlinarith [hlarge]
    have hcSq : c ^ 2 = Λ⁻¹ := by
      dsimp [c]
      exact Real.sq_sqrt (inv_nonneg.mpr (by linarith))
    have hscaled := mul_le_mul_of_nonneg_left hFG (by positivity : 0 ≤ Λ / 4)
    have hcancel : Λ / 4 * (4 * c ^ 2 * fsq D) = fsq D := by
      rw [hcSq]
      field_simp [ne_of_gt (show Λ > 0 by linarith)]
    calc
      fsq D = Λ / 4 * (4 * c ^ 2 * fsq D) := hcancel.symm
      _ ≤ Λ / 4 * fsq (A - B) := hscaled

/-- Pointwise consumer for the coefficient field in a regular environment. -/
theorem regularCoefficient_cfcSqrt_frobenius_lipschitz {d : ℕ} {Λ : ℝ}
    (hΛ : 1 ≤ Λ) (ω : FieldPair d) (hω : IsRegular Λ ω) (x y : Vec d) :
    (∑ i, ∑ j, (CFC.sqrt (ω.1 x) i j - CFC.sqrt (ω.1 y) i j) ^ 2) ≤
      Λ / 4 * (∑ i, ∑ j, (ω.1 x i j - ω.1 y i j) ^ 2) := by
  apply cfcSqrt_frobenius_lipschitz_of_ellipticity hΛ (ω.1 x) (ω.1 y)
  · simpa [IsElliptic] using hω.1 x
  · simpa [IsElliptic] using hω.1 y

end EinsteinRelation
