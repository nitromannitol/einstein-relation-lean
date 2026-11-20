import EinsteinFull.Homogenization.MultiscaleAffine
import Homogenization.Sobolev.H1.OriginCubeSymmetry

/-!
# Mean of a linear function on a centered cube

The linear function subtracted in the optimizer flatness estimate of
Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, (2.48), has zero mean on the centered cube.
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

/-- Each coordinate has zero integral on a centered triadic cube. -/
theorem integral_coord_openCubeSet_originCube {d : ℕ} (n : ℤ) (i : Fin d) :
    (∫ x in openCubeSet (originCube d n), x i ∂volume) = 0 := by
  have h := setIntegral_comp_signFlipVecContinuousLinearEquiv_openCubeSet_originCube
    i n (fun x => x i)
  simp only [signFlipVecContinuousLinearEquiv_apply, matVecMul_signFlipMatrix_apply,
    ↓reduceIte, neg_one_mul, integral_neg] at h
  linarith

/-- A linear function has zero integral on a centered triadic cube. -/
theorem integral_vecDot_openCubeSet_originCube {d : ℕ} (n : ℤ) (b : Vec d) :
    (∫ x in openCubeSet (originCube d n), vecDot b x ∂volume) = 0 := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d n))) :=
    isFiniteMeasure_openCubeSet_originCube n
  have hi (i : Fin d) : Integrable (fun x : Vec d => b i * x i)
      (volume.restrict (openCubeSet (originCube d n))) := by
    have h := (H1Function.coordOnOpenCubeSetOriginCube (n := n) i).memL2.integrable
      (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    change Integrable (fun x : Vec d => x i)
      (volume.restrict (openCubeSet (originCube d n))) at h
    exact h.const_mul (b i)
  unfold vecDot
  rw [integral_finsetSum Finset.univ (fun i _ => hi i)]
  apply Finset.sum_eq_zero
  intro i _
  rw [integral_const_mul, integral_coord_openCubeSet_originCube, mul_zero]

end EinsteinFull.Homogenization
