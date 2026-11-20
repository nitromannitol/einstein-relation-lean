import EinsteinFull.Homogenization.OriginCubeLinearNorm
import Homogenization.Deterministic.CoarseCaccioppoli.CutoffProduct.OneCube

/-!
# Changes of affine slope

The normalized `L²` deviations from two affine slopes differ by at most the
cube side length times the difference of the slopes.
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

/-- Compare the affine deviations of an `H¹` function from two slopes. -/
theorem cubeLpNorm_sub_vecDot_le_changeSlope {d : ℕ} (N : ℕ)
    (u : H1Function (openCubeSet (originCube d (N : ℤ)))) (b₀ b₁ : Vec d) :
    cubeLpNorm (originCube d (N : ℤ)) 2 (fun x => u x - vecDot b₀ x) ≤
      cubeLpNorm (originCube d (N : ℤ)) 2 (fun x => u x - vecDot b₁ x) +
      (d : ℝ) * (3 : ℝ) ^ N * Real.sqrt (vecNormSq (b₁ - b₀)) := by
  let Q := originCube d (N : ℤ)
  have hu : MemLp (fun x => u x - vecDot b₁ x) 2 (normalizedCubeMeasure Q) := by
    simpa only [H1Function.sub_toFun, affineH1_toFun] using
      (u - affineH1 (N : ℤ) b₁).memL2_normalizedCubeMeasure
  have hv : MemLp (fun x => vecDot (b₁ - b₀) x) 2 (normalizedCubeMeasure Q) := by
    simpa only [affineH1_toFun] using (affineH1 (N : ℤ) (b₁ - b₀)).memL2_normalizedCubeMeasure
  have hf : (fun x => u x - vecDot b₀ x) =
      (fun x => (u x - vecDot b₁ x) + vecDot (b₁ - b₀) x) := by
    funext x
    simp only [vecDot, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]
    ring
  calc
    _ ≤ cubeLpNorm Q 2 (fun x => u x - vecDot b₁ x) +
        cubeLpNorm Q 2 (fun x => vecDot (b₁ - b₀) x) := by
      rw [hf]
      exact cubeLpNorm_add_le Q 2 _ _ hu hv (by norm_num)
    _ ≤ _ := by gcongr; exact cubeLpNorm_vecDot_originCube_le N (b₁ - b₀)

end EinsteinFull.Homogenization
