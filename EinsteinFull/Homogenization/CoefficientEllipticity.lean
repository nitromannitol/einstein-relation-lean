import EinsteinFull.Homogenization.CoefficientL2
import Homogenization.Ambient.MatrixOrderBridge
import Homogenization.Probability.RegCoeffField.SliceMeasurability

/-!
# Ellipticity of source coefficients

The symmetric coefficient bounds in Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (0.6),
imply the inverse ellipticity bounds used by the matrix-valued coefficient carrier.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport

/-- A source coefficient satisfies the inverse ellipticity convention of the
matrix-valued carrier, with any upper constant dominating its source bound and one. -/
theorem source_isEllipticMatrix {d : ℕ} {K L : ℝ} (a : Coefficient d K)
    (hL : 1 ≤ L) (hKL : K ≤ L) (x : Vec d) :
    _root_.Homogenization.IsEllipticMatrix 1 L (a.field x) := by
  let A := a.field x
  let B : _root_.Homogenization.Mat d := Matrix.diagonal (fun _ => L)
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hA : A.PosDef := by
    apply Matrix.PosDef.of_dotProduct_mulVec_pos
    · change Matrix.conjTranspose A = A
      ext i j
      simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply] using
        congrFun (congrFun (a.symmetric x) i) j
    · intro ξ hξ
      have hpos : 0 < _root_.Homogenization.vecNormSq ξ :=
        lt_of_le_of_ne (_root_.Homogenization.vecNormSq_nonneg ξ)
          (fun heq => hξ (_root_.Homogenization.vecNormSq_eq_zero heq.symm))
      have hlower := (a.elliptic x ξ).1
      change _root_.Homogenization.vecNormSq ξ ≤
        _root_.Homogenization.vecDot ξ (_root_.Homogenization.matVecMul A ξ) at hlower
      simpa [_root_.Homogenization.vecDot, _root_.Homogenization.matVecMul,
        dotProduct, Matrix.mulVec] using lt_of_lt_of_le hpos hlower
  have hB : B.PosDef := Matrix.PosDef.diagonal (fun _ => hLpos)
  have hAB : _root_.Homogenization.MatLoewnerLE A B := by
    intro ξ
    have hbound := (a.elliptic x ξ).2
    change _root_.Homogenization.vecDot ξ (_root_.Homogenization.matVecMul A ξ) ≤
      K * _root_.Homogenization.vecNormSq ξ at hbound
    have hbound' := hbound.trans (mul_le_mul_of_nonneg_right hKL
      (_root_.Homogenization.vecNormSq_nonneg ξ))
    have hdiag : _root_.Homogenization.vecDot ξ (_root_.Homogenization.matVecMul B ξ) =
        L * _root_.Homogenization.vecNormSq ξ := by
      simp [B, _root_.Homogenization.vecDot, _root_.Homogenization.matVecMul,
        _root_.Homogenization.vecNormSq, Matrix.diagonal_apply, Finset.mul_sum, mul_left_comm]
    rw [hdiag]
    exact mul_le_mul_of_nonneg_left hbound' (by norm_num)
  have hinv := _root_.Homogenization.matLoewnerLE_inv_of_posDef hA hB hAB
  refine ⟨zero_lt_one, hL, ?_, ?_⟩
  · intro ξ
    rw [one_mul]
    change _root_.Homogenization.vecNormSq ξ ≤
      _root_.Homogenization.vecDot ξ (_root_.Homogenization.matVecMul A ξ)
    exact (a.elliptic x ξ).1
  · intro ξ
    have h := hinv ξ
    have hunit : IsUnit (fun _ : Fin d => L) :=
      Pi.isUnit_iff.mpr (fun _ => isUnit_iff_ne_zero.mpr hLpos.ne')
    have hfun : Ring.inverse (fun _ : Fin d => L) = (fun _ => L⁻¹) := by
      funext i
      apply eq_inv_of_mul_eq_one_right
      have hcancel := congrFun (Ring.mul_inverse_cancel (fun _ : Fin d => L) hunit) i
      exact hcancel
    have hdiag : _root_.Homogenization.vecDot ξ (_root_.Homogenization.matVecMul B⁻¹ ξ) =
        L⁻¹ * _root_.Homogenization.vecNormSq ξ := by
      simp [B, Matrix.inv_diagonal, hfun, _root_.Homogenization.vecDot,
        _root_.Homogenization.matVecMul, _root_.Homogenization.vecNormSq,
        Matrix.diagonal_apply, Finset.mul_sum, mul_left_comm]
    rw [hdiag] at h
    linarith

/-- Every regular representative belongs to a common quantitative ellipticity
slice on any measurable domain once the slice constant dominates the source bound. -/
theorem regularCoefficient_aeeQuantitativeEllipticSlice {d : ℕ} {K : ℝ}
    (U : Set (Vec d)) (hU : MeasurableSet U) (k : ℕ) (hK : K ≤ (k : ℝ) + 1)
    (a : Coefficient d K) :
    _root_.Homogenization.AEEQuantitativeEllipticSlice U k (regularCoefficient a).toFun := by
  apply (_root_.Homogenization.aeeQuantitativeEllipticSlice_carrier_iff U hU k
    (regularCoefficient a)).mpr
  apply ae_restrict_of_ae
  filter_upwards [regularCoefficient_ae_eq a] with x hx
  rw [hx]
  have hlarge : (1 : ℝ) ≤ (k : ℝ) + 1 := by
    linarith [Nat.cast_nonneg (α := ℝ) k]
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := lt_of_lt_of_le zero_lt_one hlarge
  exact (source_isEllipticMatrix a hlarge hK x).mono (inv_pos.mpr hpos)
    ((inv_le_one₀ hpos).2 hlarge) le_rfl

/-- The local matrix-valued L² realization is measurable for any quantitative
slice constant dominating the source bound. -/
theorem measurable_regularCoefficient_toHilbertMatrixL2_of_le {d : ℕ} {K : ℝ}
    (U : Set (Vec d)) [IsFiniteMeasure (_root_.Homogenization.volumeMeasureOn U)]
    (hU : IsOpen U) (k : ℕ) (hK : K ≤ (k : ℝ) + 1) :
    @Measurable (Coefficient d K)
      (Lp (_root_.Homogenization.HilbertMat d) 2 (_root_.Homogenization.volumeMeasureOn U))
      (localSigma U) (borel _)
      (fun a => _root_.Homogenization.AEEQuantitativeEllipticSlice.toHilbertMatrixL2
        (_root_.Homogenization.rawSlice regularCoefficient
          (regularCoefficient_aeeQuantitativeEllipticSlice U hU.measurableSet k hK) a)) :=
  measurable_regularCoefficient_toHilbertMatrixL2 U hU k
    (regularCoefficient_aeeQuantitativeEllipticSlice U hU.measurableSet k hK)

end EinsteinFull.Homogenization
