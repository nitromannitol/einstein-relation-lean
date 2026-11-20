import EinsteinFull.Regeneration.EllipticComplement

/-!
# Harnack lower bound on the central cube

The pointwise comparison gives the quantitative central-cube lower bound in
Gantert–Mathieu–Piatnitski, Lemma 4.4, immediately before (4.12).
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Coordinates in the unit cube have squared Euclidean norm at most the dimension. -/
theorem euclideanSqDist_zero_le_dim_of_abs_le_one {d : ℕ} (z : PDE.Vec d)
    (hz : ∀ i, |z i| ≤ 1) : PDE.euclideanSqDist 0 z ≤ d := by
  unfold PDE.euclideanSqDist PDE.vecNormSq PDE.vecDot
  calc
    (∑ i : Fin d, (0 - z) i * (0 - z) i) ≤ ∑ _i : Fin d, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      have h := abs_le.mp (hz i)
      simp only [Pi.sub_apply, Pi.zero_apply]
      nlinarith
    _ = d := by simp

/-- A small value at the center forces a uniform positive complement on the central cube. -/
theorem gmp_central_cube_complement_lower (d : ℕ) (hd : 0 < d) (lam Λ : ℝ)
    (hlam : 0 < lam) (hΛ : lam ≤ Λ) :
    ∃ c : ℝ, 0 < c ∧ ∀ (i : Fin d) (z : PDE.Vec d), z i = 0 →
      (∀ j, |z j| ≤ 1) →
      let U := PDE.euclideanBall ((1 / 2 : ℝ) • ((0 : PDE.Vec d) + z))
        (Real.sqrt (8 * d))
      ∀ a : PDE.CoeffField d,
      (∀ j k, AEMeasurable (fun x => a x j k) (volume.restrict U)) →
      (∀ᵐ x ∂(volume.restrict U), PDE.IsEllipticMatrix lam Λ (a x)) →
      ∀ u : PDE.H1Function U,
      PDE.IsWeakDivergenceFormL2SolutionOn (fun x => Real.exp (x i) • a x) U u 0 0 →
      Continuous u.toFun → (∀ x, u x ≤ 1) → u 0 < 2 / 3 → c ≤ 1 - u z := by
  obtain ⟨H, hH, hcomp⟩ := gmp_central_slab_complement_harnack d hd lam Λ hlam hΛ
  have hHpos : 0 < H := by linarith
  refine ⟨1 / (3 * H), by positivity, ?_⟩
  intro i z hzi hz
  dsimp only
  intro a hmeas hell u hsol hcont hupper hsmall
  have h := hcomp i 0 z (by simp) hzi (euclideanSqDist_zero_le_dim_of_abs_le_one z hz)
  dsimp only at h
  have hh := h a hmeas hell u hsol hcont hupper
  apply (div_le_iff₀ (by positivity : 0 < 3 * H)).2
  nlinarith

end EinsteinFull.Regeneration
