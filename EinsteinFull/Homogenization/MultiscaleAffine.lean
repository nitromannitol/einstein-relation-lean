import EinsteinFull.Homogenization.MultiscalePoincareVector
import Homogenization.HighContrast.Coupled.WeakForm

/-!
# Multiscale Poincaré inequality for affine deviations

Applying the vector multiscale Poincaré inequality to the difference between
an `H¹` function and a linear function gives the deterministic estimate used
in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, (2.48).
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

/-- An affine deviation is controlled by the normalized `L²` norm and
multiscale averages of its gradient deviation. -/
theorem exists_originCube_multiscalePoincare_affine (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (u : H1Function (openCubeSet (originCube d (n : ℤ))))
      (b : Vec d),
      (∀ j, ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) j, ∀ i,
        Integrable (fun x => u.grad x i - b i) (normalizedCubeMeasure R)) ∧
      MemLp (fun x => euclideanNorm (u.grad x - b)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d (n : ℤ))) ∧
      cubeBesovOscillation (originCube d (n : ℤ)) (2 : ℝ≥0∞)
        (fun x => u x - vecDot b x) ≤
        C * (cubeLpNorm (originCube d (n : ℤ)) (2 : ℝ≥0∞)
          (fun x => euclideanNorm (u.grad x - b)) +
          ∑ j ∈ Finset.range (n + 1), (3 : ℝ) ^ (n - j) *
            Real.sqrt (descendantsAverage (originCube d (n : ℤ)) j
              (fun R => vecNormSq (fun i => cubeAverage R (fun x => u.grad x i) - b i)))) := by
  obtain ⟨C, hC, h⟩ := exists_originCube_multiscalePoincare d
  refine ⟨C, hC, ?_⟩
  intro n u b
  let w : H1Function (openCubeSet (originCube d (n : ℤ))) := u - affineH1 (n : ℤ) b
  have hw : w.toFun = fun x => u x - vecDot b x := by
    simp only [w, H1Function.sub_toFun, affineH1_toFun]
  have hg : w.grad = fun x => u.grad x - b := by
    simp only [w, H1Function.sub_grad, affineH1_grad]
  have hw' := h n w
  simp only [hw, hg, Pi.sub_apply] at hw'
  refine ⟨hw'.1, hw'.2.1, ?_⟩
  refine hw'.2.2.trans_eq ?_
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  congr 1
  dsimp only [descendantsAverage]
  congr 1
  apply Finset.sum_congr rfl
  intro R hR
  congr 1
  funext i
  have hG := memLp_on_descendant_of_memLp hR (u.grad_coord_memL2_normalizedCubeMeasure i)
  exact cubeAverage_sub_const_of_memLp_two R hG (b i)

end EinsteinFull.Homogenization
