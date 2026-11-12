import EinsteinRelation.Correctors.AKMTestConvolution
import EinsteinRelation.Mobility.DriftBoundPointwise

/-! # Uniform bounds for actual source coefficient averages

Source: `paper/main.tex:789–798`. Nonnegative normalized smooth averages of
coefficient entries retain their deterministic ellipticity bound. These
are genuine source observables, rather than unmeasurable point evaluations.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors
open Environment.AKMTestIntegralSupport

/-- Smooth averaging retains the coefficient entry bound before selecting
any probability law. Source: `paper/main.tex:789–798`. -/
theorem abs_coefficientTestConvolution_le {d : ℕ} {K : ℝ} (hK : 0 ≤ K)
    (κ : SmoothCompactTest d) (hκ : ∀ x, 0 ≤ κ x)
    (hκ1 : (∫ x, κ x) = 1) (A : Coefficient d K) (x : Vec d) (i j : Fin d) :
    |coefficientTestConvolution κ A x i j| ≤ K := by
  let u : SmoothCompactTest d :=
    ⟨fun y => κ (x - y), κ.smooth.comp (contDiff_const.sub contDiff_id),
      κ.compact.comp_homeomorph (Homeomorph.subLeft x)⟩
  have hentry (y : Vec d) : |A y i j| ≤ K := by
    apply abs_entry_le_of_quadratic_bounds hK (A y) (A.symmetric y)
    · intro ξ
      exact (show 0 ≤ euclideanSq ξ from by
        change 0 ≤ ∑ k, ξ k * ξ k
        exact Finset.sum_nonneg fun k _ => mul_self_nonneg _).trans (A.elliptic y ξ).1
    · exact fun ξ => (A.elliptic y ξ).2
  have huint : Integrable (fun y => κ (x - y)) volume :=
    u.smooth.continuous.integrable_of_hasCompactSupport u.compact
  have hint : (∫ y, κ (x - y)) = 1 := by
    rw [integral_sub_left_eq_self, hκ1]
  calc
    _ ≤ ∫ y, |κ (x - y) * A y i j| := abs_integral_le_integral_abs
    _ ≤ ∫ y, κ (x - y) * K := by
      apply integral_mono (integrable_testIntegrand A u i j).abs (huint.mul_const K)
      intro y
      change |κ (x - y) * A y i j| ≤ κ (x - y) * K
      rw [abs_mul, abs_of_nonneg (hκ _)]
      exact mul_le_mul_of_nonneg_left (hentry y) (hκ _)
    _ = K := by rw [integral_mul_const, hint, one_mul]

end EinsteinRelation.Correctors
