import EinsteinFull.Homogenization.MultiscaleVectorAverages

/-!
# Vector multiscale Poincaré inequality

The oscillation of an `H¹` function is bounded by its gradient's `L²` norm
and the Euclidean root mean squares of its block averages, as in Armstrong,
Kuusi and Mourrat, *Quantitative Stochastic Homogenization and Large-Scale
Regularity*, Corollary 1.14.
-/

open scoped ENNReal
open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

/-- A dimension-only multiscale Poincaré bound on triadic origin cubes, with
all block-average integrability and the Euclidean gradient `L²` fact included. -/
theorem exists_originCube_multiscalePoincare (d : ℕ) [NeZero d] :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℕ) (u : H1Function (openCubeSet (originCube d (n : ℤ)))),
      (∀ j, ∀ R ∈ descendantsAtDepth (originCube d (n : ℤ)) j, ∀ i,
        Integrable (fun x => u.grad x i) (normalizedCubeMeasure R)) ∧
      MemLp (fun x => euclideanNorm (u.grad x)) (2 : ℝ≥0∞)
        (normalizedCubeMeasure (originCube d (n : ℤ))) ∧
      cubeBesovOscillation (originCube d (n : ℤ)) (2 : ℝ≥0∞) (fun x => u x) ≤
        C * (cubeLpNorm (originCube d (n : ℤ)) (2 : ℝ≥0∞)
          (fun x => euclideanNorm (u.grad x)) +
          ∑ j ∈ Finset.range (n + 1), (3 : ℝ) ^ (n - j) *
            Real.sqrt (descendantsAverage (originCube d (n : ℤ)) j
              (fun R => vecNormSq (fun i => cubeAverage R (fun x => u.grad x i))))) := by
  let C₀ : ℝ := Book.Ch01.Legacy.fullVectorPoincareConstant (originCube d 0) *
    (3 : ℝ) ^ ((d : ℝ) + 1)
  have hC : 0 ≤ C₀ := mul_nonneg
    (Book.Ch01.Legacy.fullVectorPoincareConstant_nonneg _) (by positivity)
  refine ⟨C₀ * d, mul_nonneg hC (Nat.cast_nonneg d), ?_⟩
  intro n u
  let Q := originCube d (n : ℤ)
  let V : ℕ → ℝ := fun j => (3 : ℝ) ^ (n - j) *
    Real.sqrt (descendantsAverage Q j
      (fun R => vecNormSq (fun i => cubeAverage R (fun x => u.grad x i))))
  let L : ℝ := cubeLpNorm Q (2 : ℝ≥0∞) (fun x => euclideanNorm (u.grad x))
  have hG (i : Fin d) : MemLp (fun x => u.grad x i) (2 : ℝ≥0∞)
      (normalizedCubeMeasure Q) := u.grad_coord_memL2_normalizedCubeMeasure i
  have hI : ∀ j, ∀ R ∈ descendantsAtDepth Q j, ∀ i,
      Integrable (fun x => u.grad x i) (normalizedCubeMeasure R) := by
    intro j R hR i
    exact (memLp_on_descendant_of_memLp hR (hG i)).integrable (by norm_num)
  obtain ⟨hmem, hgrad⟩ := memLp_and_cubeLpNorm_grad_coord_le_euclidean Q u
  refine ⟨hI, hmem, ?_⟩
  have hL : 0 ≤ L := cubeLpNorm_nonneg _ _ _
  have hterm (i : Fin d) :
      (∑ j ∈ Finset.range (n + 1),
        cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j) +
      (1 / 2 : ℝ) * cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.grad x i) ≤
      L + ∑ j ∈ Finset.range (n + 1), V j := by
    have hs : (∑ j ∈ Finset.range (n + 1),
        cubeBesovCircDepthSeminorm Q 1 (2 : ℝ≥0∞) (fun x => u.grad x i) j) ≤
        ∑ j ∈ Finset.range (n + 1), V j := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := by simp only [Finset.mem_range] at hj; omega
      exact (integrable_and_originCubeBesovDepth_le_vector n j hjn u.grad hG).2 i
    have hl := hgrad i
    change cubeLpNorm Q (2 : ℝ≥0∞) (fun x => u.grad x i) ≤ L at hl
    linarith
  have hconst : Book.Ch01.Legacy.fullVectorPoincareConstant Q *
      (3 : ℝ) ^ ((d : ℝ) + 1) = C₀ := by
    rfl
  have h := originCubeBesovOscillation_le_sum_scales_add_gradient n u
  change cubeBesovOscillation Q (2 : ℝ≥0∞) (fun x => u x) ≤ _ at h
  rw [hconst] at h
  calc
    _ ≤ _ := h
    _ ≤ C₀ * ∑ _i : Fin d, (L + ∑ j ∈ Finset.range (n + 1), V j) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hterm i)) hC
    _ = _ := by simp only [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]; ring

end EinsteinFull.Homogenization
