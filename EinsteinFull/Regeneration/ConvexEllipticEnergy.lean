import EinsteinFull.Regeneration.SlabEnergyMinimality
import PDEFoundation.Ambient.CoefficientField

/-!
# Convex combinations in symmetric elliptic energy

A symmetric nonnegative quadratic energy is convex, and its bilinear pairing
is bounded by the ellipticity upper constant.
-/

open PDE

namespace EinsteinFull.Regeneration

/-- Quadratic energy of a vector for a coefficient matrix. -/
def matrixEnergy {d : ℕ} (A : PDE.Mat d) (v : PDE.Vec d) : ℝ :=
  PDE.vecDot (PDE.matVecMul A v) v

/-- Scaling a vector scales its quadratic energy by the square. -/
theorem matrixEnergy_smul {d : ℕ} (A : PDE.Mat d) (c : ℝ) (v : PDE.Vec d) :
    matrixEnergy A (c • v) = c ^ 2 * matrixEnergy A v := by
  unfold matrixEnergy
  rw [show PDE.matVecMul A (c • v) = c • PDE.matVecMul A v from Matrix.mulVec_smul A c v,
    PDE.DGNM.vecDot_smul_left, PDE.DGNM.vecDot_smul_right]
  ring

/-- Symmetric quadratic energy has the usual cross-term expansion. -/
theorem matrixEnergy_add {d : ℕ} (A : PDE.Mat d) (hA : A.IsSymm)
    (v w : PDE.Vec d) :
    matrixEnergy A (v + w) = matrixEnergy A v +
      2 * PDE.vecDot (PDE.matVecMul A v) w + matrixEnergy A w :=
  symmetric_energy_add A hA v w

/-- Symmetric nonnegative quadratic energy is convex. -/
theorem matrixEnergy_convex_le {d : ℕ} (A : PDE.Mat d) (hA : A.IsSymm)
    (hpos : ∀ v, 0 ≤ matrixEnergy A v) (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    (v w : PDE.Vec d) :
    matrixEnergy A (θ • v + (1 - θ) • w) ≤
      θ * matrixEnergy A v + (1 - θ) * matrixEnergy A w := by
  have hsub : matrixEnergy A (v - w) = matrixEnergy A v -
      2 * PDE.vecDot (PDE.matVecMul A v) w + matrixEnergy A w := by
    have h := matrixEnergy_add A hA v ((-1 : ℝ) • w)
    rw [matrixEnergy_smul, PDE.DGNM.vecDot_smul_right] at h
    simp only [neg_one_smul, sub_eq_add_neg] at h ⊢
    nlinarith [h]
  have hadd := matrixEnergy_add A hA (θ • v) ((1 - θ) • w)
  have hm : PDE.matVecMul A (θ • v) = θ • PDE.matVecMul A v := Matrix.mulVec_smul A θ v
  rw [matrixEnergy_smul, matrixEnergy_smul, hm, PDE.DGNM.vecDot_smul_left,
    PDE.DGNM.vecDot_smul_right] at hadd
  have hnonneg : 0 ≤ θ * (1 - θ) * matrixEnergy A (v - w) :=
    mul_nonneg (mul_nonneg hθ0 (sub_nonneg.mpr hθ1)) (hpos _)
  nlinarith [hsub, hadd]

/-- Ellipticity bounds a coefficient pairing by the Euclidean vector norms. -/
theorem abs_matrix_pairing_le {d : ℕ} {lam Λ : ℝ} {A : PDE.Mat d}
    (hA : PDE.IsEllipticMatrix lam Λ A) (v w : PDE.Vec d) :
    |PDE.vecDot (PDE.matVecMul A v) w| ≤
      Λ * PDE.vecEuclideanNorm v * PDE.vecEuclideanNorm w := by
  calc
    _ ≤ PDE.vecEuclideanNorm (PDE.matVecMul A v) * PDE.vecEuclideanNorm w :=
      PDE.abs_vecDot_le_vecEuclideanNorm_mul _ _
    _ ≤ (Λ * PDE.vecEuclideanNorm v) * PDE.vecEuclideanNorm w :=
      mul_le_mul_of_nonneg_right (PDE.vecEuclideanNorm_matVecMul_le_of_isEllipticMatrix hA v)
        (PDE.vecEuclideanNorm_nonneg w)


/-- Adding an error vector to a convex combination gives the shell energy bound. -/
theorem matrixEnergy_convex_add_le {d : ℕ} {lam Λ : ℝ} {A : PDE.Mat d}
    (hA : PDE.IsEllipticMatrix lam Λ A) (hsym : A.IsSymm)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) (v w z : PDE.Vec d) :
    matrixEnergy A (θ • v + (1 - θ) • w + z) ≤
      matrixEnergy A v + matrixEnergy A w + Λ * (PDE.vecEuclideanNorm z) ^ 2 +
        2 * Λ * PDE.vecEuclideanNorm z *
          (PDE.vecEuclideanNorm v + PDE.vecEuclideanNorm w) := by
  let m : PDE.Vec d := θ • v + (1 - θ) • w
  have hpos (x : PDE.Vec d) : 0 ≤ matrixEnergy A x := by
    have h := hA.coercive x
    have h0 := mul_nonneg hA.lam_pos.le (PDE.vecNormSq_nonneg x)
    exact h0.trans (by simpa only [matrixEnergy, PDE.vecDot_comm] using h)
  have hmix : matrixEnergy A m ≤ matrixEnergy A v + matrixEnergy A w := by
    have h := matrixEnergy_convex_le A hsym hpos θ hθ0 hθ1 v w
    have hv := mul_nonneg (sub_nonneg.mpr hθ1) (hpos v)
    have hw := mul_nonneg hθ0 (hpos w)
    dsimp only [m]
    nlinarith [h, hv, hw]
  have hnorm : PDE.vecEuclideanNorm m ≤ PDE.vecEuclideanNorm v + PDE.vecEuclideanNorm w := by
    have htri := PDE.vecEuclideanNorm_add_le (θ • v) ((1 - θ) • w)
    rw [PDE.vecEuclideanNorm_smul, PDE.vecEuclideanNorm_smul,
      abs_of_nonneg hθ0, abs_of_nonneg (sub_nonneg.mpr hθ1)] at htri
    have hv := PDE.vecEuclideanNorm_nonneg v
    have hw := PDE.vecEuclideanNorm_nonneg w
    dsimp only [m]
    nlinarith [mul_nonneg (sub_nonneg.mpr hθ1) hv, mul_nonneg hθ0 hw]
  have hz : matrixEnergy A z ≤ Λ * (PDE.vecEuclideanNorm z) ^ 2 := by
    have h := (le_abs_self (PDE.vecDot (PDE.matVecMul A z) z)).trans
      (abs_matrix_pairing_le hA z z)
    dsimp only [matrixEnergy]
    nlinarith [h]
  have hcross : PDE.vecDot (PDE.matVecMul A m) z ≤
      Λ * (PDE.vecEuclideanNorm v + PDE.vecEuclideanNorm w) * PDE.vecEuclideanNorm z := by
    have h := (le_abs_self (PDE.vecDot (PDE.matVecMul A m) z)).trans
      (abs_matrix_pairing_le hA m z)
    have hscale := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hnorm hA.Lam_pos.le) (PDE.vecEuclideanNorm_nonneg z)
    exact h.trans hscale
  have heq := matrixEnergy_add A hsym m z
  change matrixEnergy A (m + z) ≤ _
  nlinarith [heq, hmix, hz, hcross]

end EinsteinFull.Regeneration
