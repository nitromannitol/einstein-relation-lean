import EinsteinRelation.Environment.Basic
import Homogenization.CoarseGraining.BlockFormalism

/-!
# Symmetric block energy

For symmetric coefficients the doubled energy of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
splits into independent potential and flux quadratic energies.
-/

namespace EinsteinFull.Homogenization

open EinsteinRelation

/-- The doubled energy for a symmetric coefficient splits into a Dirichlet
energy and an inverse-coefficient flux energy. -/
theorem symmetric_blockEnergyDensity {d : ℕ}
    (a : _root_.Homogenization.CoeffField d) (X : _root_.Homogenization.BlockState d)
    (x : Vec d) (ha : (a x).transpose = a x) :
    _root_.Homogenization.blockEnergyDensity a X x =
      (1 / 2 : ℝ) * dot (X.potential x) ((a x).mulVec (X.potential x)) +
      (1 / 2 : ℝ) * dot (X.flux x) (((a x)⁻¹).mulVec (X.flux x)) := by
  have hs : _root_.Homogenization.symmPart (a x) = a x := by
    ext i j
    have hij := congrFun (congrFun ha i) j
    simp only [Matrix.transpose_apply] at hij
    simp only [_root_.Homogenization.symmPart]
    rw [hij]
    ring
  have hk : _root_.Homogenization.skewPart (a x) = 0 := by
    ext i j
    have hij := congrFun (congrFun ha i) j
    simp only [Matrix.transpose_apply] at hij
    simp only [_root_.Homogenization.skewPart, Matrix.zero_apply]
    rw [hij]
    ring
  unfold _root_.Homogenization.blockEnergyDensity _root_.Homogenization.blockCoeffField
  rw [_root_.Homogenization.BlockState.eval,
    _root_.Homogenization.blockMatrixOfCoeff_quadratic_eq, hs, hk]
  simp [_root_.Homogenization.matVecMul, _root_.Homogenization.vecDot,
    dot, Matrix.mulVec, dotProduct]
  ring

/-- In a symmetric elliptic medium the potential energy is bounded above by
the doubled energy, regardless of the flux component. -/
theorem potentialEnergy_le_symmetric_blockEnergyDensity {d : ℕ} {lam Lam : ℝ}
    (a : _root_.Homogenization.CoeffField d) (X : _root_.Homogenization.BlockState d)
    (x : Vec d) (ha : (a x).transpose = a x)
    (hEll : _root_.Homogenization.IsEllipticMatrix lam Lam (a x)) :
    (1 / 2 : ℝ) * dot (X.potential x) ((a x).mulVec (X.potential x)) ≤
      _root_.Homogenization.blockEnergyDensity a X x := by
  rw [symmetric_blockEnergyDensity a X x ha]
  have hLam : 0 < Lam := lt_of_lt_of_le hEll.1 hEll.2.1
  have hflux := hEll.2.2.2 (X.flux x)
  have hnonneg : 0 ≤ _root_.Homogenization.vecDot (X.flux x)
      (_root_.Homogenization.matVecMul ((a x)⁻¹) (X.flux x)) :=
    (mul_nonneg (inv_nonneg.mpr hLam.le)
      (_root_.Homogenization.vecNormSq_nonneg _)).trans hflux
  change 0 ≤ dot (X.flux x) (((a x)⁻¹).mulVec (X.flux x)) at hnonneg
  nlinarith

/-- With zero flux, the doubled energy equals the potential energy. -/
theorem symmetric_blockEnergyDensity_of_flux_eq_zero {d : ℕ}
    (a : _root_.Homogenization.CoeffField d) (X : _root_.Homogenization.BlockState d)
    (x : Vec d) (ha : (a x).transpose = a x) (hflux : X.flux x = 0) :
    _root_.Homogenization.blockEnergyDensity a X x =
      (1 / 2 : ℝ) * dot (X.potential x) ((a x).mulVec (X.potential x)) := by
  rw [symmetric_blockEnergyDensity a X x ha, hflux]
  simp [dot]

end EinsteinFull.Homogenization
