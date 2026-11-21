import EinsteinFull.Regeneration.ConvexEllipticEnergy

/-!
# Pointwise estimate for a squared slab cutoff

The derivative of a squared cutoff carries one factor of the cutoff.  This
factor permits the gradient cross term to be absorbed by ellipticity.
-/

open PDE

namespace EinsteinFull.Regeneration

/-- A squared cutoff leaves a positive fraction of the original energy on
the left, at the cost of a quadratic cutoff-gradient error. -/
theorem matrixEnergy_squared_cutoff_le {d : ℕ} {lam Λ : ℝ} {A : PDE.Mat d}
    (hA : PDE.IsEllipticMatrix lam Λ A) (hsym : A.IsSymm)
    (η : ℝ) (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (v g z : PDE.Vec d) :
    matrixEnergy A (η ^ 2 • v + (1 - η ^ 2) • g + η • z) ≤
      (1 - η ^ 2 / 2) * matrixEnergy A g +
        (3 * η ^ 2 / 2) * matrixEnergy A v +
        (Λ + 4 * Λ ^ 2 / lam) * (PDE.vecEuclideanNorm z) ^ 2 := by
  let m : PDE.Vec d := η ^ 2 • v + (1 - η ^ 2) • g
  let V := PDE.vecEuclideanNorm v
  let G := PDE.vecEuclideanNorm g
  let Z := PDE.vecEuclideanNorm z
  have hηsq : η ^ 2 ≤ 1 := by nlinarith
  have hηsq0 : 0 ≤ η ^ 2 := sq_nonneg η
  have hV : 0 ≤ V := PDE.vecEuclideanNorm_nonneg _
  have hG : 0 ≤ G := PDE.vecEuclideanNorm_nonneg _
  have hZ : 0 ≤ Z := PDE.vecEuclideanNorm_nonneg _
  have hpos (x : PDE.Vec d) : 0 ≤ matrixEnergy A x := by
    have h := hA.coercive x
    have h0 := mul_nonneg hA.lam_pos.le (PDE.vecNormSq_nonneg x)
    exact h0.trans (by simpa only [matrixEnergy, PDE.vecDot_comm] using h)
  have hmix : matrixEnergy A m ≤ η ^ 2 * matrixEnergy A v +
      (1 - η ^ 2) * matrixEnergy A g :=
    matrixEnergy_convex_le A hsym hpos (η ^ 2) hηsq0 hηsq v g
  have hm : PDE.vecEuclideanNorm m ≤ V + G := by
    have h := PDE.vecEuclideanNorm_add_le (η ^ 2 • v) ((1 - η ^ 2) • g)
    rw [PDE.vecEuclideanNorm_smul, PDE.vecEuclideanNorm_smul,
      abs_of_nonneg hηsq0, abs_of_nonneg (sub_nonneg.mpr hηsq)] at h
    dsimp only [m, V, G] at *
    nlinarith [mul_nonneg (sub_nonneg.mpr hηsq) hV, mul_nonneg hηsq0 hG]
  have hcross : PDE.vecDot (PDE.matVecMul A m) (η • z) ≤ Λ * (V + G) * (η * Z) := by
    have h := (le_abs_self _).trans (abs_matrix_pairing_le hA m (η • z))
    rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg hη0] at h
    have h' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hm hA.Lam_pos.le) (mul_nonneg hη0 hZ)
    exact h.trans h'
  have hz : matrixEnergy A (η • z) ≤ Λ * (η * Z) ^ 2 := by
    have h := (le_abs_self _).trans (abs_matrix_pairing_le hA (η • z) (η • z))
    rw [PDE.vecEuclideanNorm_smul, abs_of_nonneg hη0] at h
    dsimp only [matrixEnergy]
    nlinarith [h]
  have hvco : lam * V ^ 2 ≤ matrixEnergy A v := by
    have h := hA.coercive v
    simpa only [V, PDE.vecEuclideanNorm_sq, matrixEnergy, PDE.vecDot_comm] using h
  have hgco : lam * G ^ 2 ≤ matrixEnergy A g := by
    have h := hA.coercive g
    simpa only [G, PDE.vecEuclideanNorm_sq, matrixEnergy, PDE.vecDot_comm] using h
  have hyoungV : 2 * Λ * η * Z * V ≤ lam / 2 * (η * V) ^ 2 +
      2 * Λ ^ 2 / lam * Z ^ 2 := by
    have h := mul_nonneg (div_nonneg hA.lam_pos.le (by norm_num : (0 : ℝ) ≤ 2))
      (sq_nonneg (η * V - (2 * Λ / lam) * Z))
    have hid : lam / 2 * (η * V - (2 * Λ / lam) * Z) ^ 2 =
        lam / 2 * (η * V) ^ 2 - 2 * Λ * η * Z * V + 2 * Λ ^ 2 / lam * Z ^ 2 := by
      field_simp [ne_of_gt hA.lam_pos]
      ring
    linarith
  have hyoungG : 2 * Λ * η * Z * G ≤ lam / 2 * (η * G) ^ 2 +
      2 * Λ ^ 2 / lam * Z ^ 2 := by
    have h := mul_nonneg (div_nonneg hA.lam_pos.le (by norm_num : (0 : ℝ) ≤ 2))
      (sq_nonneg (η * G - (2 * Λ / lam) * Z))
    have hid : lam / 2 * (η * G - (2 * Λ / lam) * Z) ^ 2 =
        lam / 2 * (η * G) ^ 2 - 2 * Λ * η * Z * G + 2 * Λ ^ 2 / lam * Z ^ 2 := by
      field_simp [ne_of_gt hA.lam_pos]
      ring
    linarith
  have hv' := mul_le_mul_of_nonneg_left hvco hηsq0
  have hg' := mul_le_mul_of_nonneg_left hgco hηsq0
  have hz' := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hηsq (sq_nonneg Z)) hA.Lam_pos.le
  have heq := matrixEnergy_add A hsym m (η • z)
  change matrixEnergy A (m + η • z) ≤
    (1 - η ^ 2 / 2) * matrixEnergy A g +
      (3 * η ^ 2 / 2) * matrixEnergy A v + (Λ + 4 * Λ ^ 2 / lam) * Z ^ 2
  ring_nf at hmix hcross hz hv' hg' hz' hyoungV hyoungG heq ⊢
  linarith only [hmix, hcross, hz, hv', hg', hz', hyoungV, hyoungG, heq]

end EinsteinFull.Regeneration
