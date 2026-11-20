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

/-- Subtracting a linear function preserves the zero mean of an `H¹` function
on a centered cube. -/
theorem cubeAverage_sub_vecDot_eq_zero {d : ℕ} (n : ℤ)
    (u : H1Function (openCubeSet (originCube d n))) (hu : MeanZeroOn
      (openCubeSet (originCube d n)) u.toFun) (b : Vec d) :
    cubeAverage (originCube d n) (fun x => u x - vecDot b x) = 0 := by
  let : IsFiniteMeasure (volumeMeasureOn (openCubeSet (originCube d n))) :=
    isFiniteMeasure_openCubeSet_originCube n
  have hu_int : Integrable u.toFun (volume.restrict (openCubeSet (originCube d n))) :=
    u.memL2.integrable (by norm_num)
  have hb_int : Integrable (fun x => vecDot b x)
      (volume.restrict (openCubeSet (originCube d n))) := by
    have h := (affineH1 n b).memL2.integrable (by norm_num : (1 : ℝ≥0∞) ≤ 2)
    simpa only [affineH1_toFun] using h
  rw [cubeAverage_eq_integralAverage_openCubeSet]
  unfold integralAverage
  rw [integral_sub hu_int hb_int, hu, integral_vecDot_openCubeSet_originCube]
  simp

/-- For a mean-zero `H¹` function, centered oscillation of the affine
remainder equals its normalized cube `L²` norm. -/
theorem cubeBesovOscillation_sub_vecDot_eq_cubeLpNorm {d : ℕ} (n : ℤ)
    (u : H1Function (openCubeSet (originCube d n))) (hu : MeanZeroOn
      (openCubeSet (originCube d n)) u.toFun) (b : Vec d) :
    cubeBesovOscillation (originCube d n) (2 : ℝ≥0∞)
      (fun x => u x - vecDot b x) =
    cubeLpNorm (originCube d n) (2 : ℝ≥0∞) (fun x => u x - vecDot b x) := by
  unfold cubeBesovOscillation cubeFluctuation
  rw [cubeAverage_sub_vecDot_eq_zero n u hu b]
  simp only [sub_zero]

end EinsteinFull.Homogenization
