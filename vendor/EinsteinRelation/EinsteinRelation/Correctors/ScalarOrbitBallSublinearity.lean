import EinsteinRelation.Correctors.ScalarOrbitIntegerSublinearity
import EinsteinRelation.Correctors.ScalarOrbitLocalL2
import EinsteinRelation.Correctors.EuclideanBallAverageComparison
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Full-radius sublinearity of stationary scalar L² orbits

Source: `paper/main.tex:693-698`. The integer-radius summability argument
extends to every real Euclidean radius through nested spatial regions and
a dimension-only volume ratio.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.Correctors
open External.AKM

/-- Vanishing nonnegative scaled integer-cube averages imply vanishing
scaled averages on all real Euclidean balls. -/
theorem ball_scaled_means_zero_of_integerCube_scaled_means_zero {d : ℕ}
    (f : Vec d → ℝ) (hf : ∀ x, 0 ≤ f x)
    (hi : ∀ R : ℝ, 0 < R → IntegrableOn f (Metric.closedBall 0 R) volume)
    (hlim : Tendsto (fun n : ℕ => (((n : ℝ) + 1)^2)⁻¹ *
      (⨍ x in Metric.closedBall (0 : Vec d) ((n : ℝ) + 1), f x ∂volume)) atTop (𝓝 0)) :
    Tendsto (fun R : ℝ => (R^2)⁻¹ * (⨍ x in ball 0 R, f x ∂volume))
      atTop (𝓝 0) := by
  obtain ⟨C, hC, hcompare⟩ := exists_ball_average_le_cube_average d
  have hfloor : Tendsto (fun R : ℝ => ⌊R⌋₊) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    exact (eventually_ge_atTop (n : ℝ)).mono fun R hR => Nat.le_floor hR
  have ht := (hlim.comp hfloor).const_mul (4 * C)
  simp only [mul_zero] at ht
  have hnonneg (R : ℝ) : 0 ≤ (R^2)⁻¹ * (⨍ x in ball 0 R, f x ∂volume) :=
    mul_nonneg (inv_nonneg.mpr (sq_nonneg R))
      (by rw [average_eq, smul_eq_mul]; exact mul_nonneg (by positivity) (integral_nonneg hf))
  apply squeeze_zero' (Eventually.of_forall hnonneg) ?_ ht
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with R hR
  have hRpos : 0 < R := zero_lt_one.trans_le hR
  let n : ℕ := ⌊R⌋₊
  let r : ℝ := (n : ℝ) + 1
  have hrpos : 0 < r := by dsimp [r]; positivity
  have hlow : R ≤ r := (Nat.lt_floor_add_one R).le
  have hhigh : r ≤ 2 * R := by
    have hfl : (n : ℝ) ≤ R := Nat.floor_le hRpos.le
    dsimp [r]
    linarith
  have hweight : (R ^ 2)⁻¹ ≤ 4 * (r ^ 2)⁻¹ := by
    simp only [← one_div, mul_one_div]
    apply (div_le_div_iff₀ (sq_pos_of_pos hRpos) (sq_pos_of_pos hrpos)).mpr
    have hs := (sq_le_sq₀ hrpos.le (show 0 ≤ 2 * R by positivity)).mpr hhigh
    nlinarith only [hs]
  have ha : 0 ≤ ⨍ x in Metric.closedBall (0 : Vec d) r, f x ∂volume := by
    rw [average_eq, smul_eq_mul]
    exact mul_nonneg (by positivity) (integral_nonneg hf)
  calc
    _ ≤ (R^2)⁻¹ * (C * (⨍ x in Metric.closedBall (0 : Vec d) r, f x ∂volume)) :=
      mul_le_mul_of_nonneg_left (hcompare R r hRpos hlow hhigh f hf (hi r hrpos))
        (inv_nonneg.mpr (sq_nonneg R))
    _ ≤ (4 * (r^2)⁻¹) * (C * (⨍ x in Metric.closedBall (0 : Vec d) r, f x ∂volume)) :=
      mul_le_mul_of_nonneg_right hweight (mul_nonneg hC.le ha)
    _ = _ := by dsimp [r, n]; ring

/-- Every stationary scalar L² orbit has vanishing uncentered scaled
second moment on the full continuum of Euclidean ball radii. -/
theorem ae_scalar_orbit_ball_scaled_mean_square_zero {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : Lp ℝ 2 Q) :
    ∀ᵐ ω ∂Q, Tendsto (fun R : ℝ => (R^2)⁻¹ *
      (⨍ x in ball 0 R, |f (translate x ω)| ^ 2 ∂volume)) atTop (𝓝 0) := by
  filter_upwards [ae_scalar_orbit_integer_scaled_mean_square_zero Q hQ f,
    ae_scalar_orbit_memLp_on_all_compacts Q hQ f] with ω hω hfω
  apply ball_scaled_means_zero_of_integerCube_scaled_means_zero _ (fun _ => sq_nonneg _) ?_ hω
  intro R hR
  have hm := hfω (Metric.closedBall (0 : Vec d) R) (isCompact_closedBall _ _)
  simpa only [Real.norm_eq_abs, IntegrableOn] using
    (memLp_two_iff_integrable_sq_norm hm.aestronglyMeasurable).mp hm

end EinsteinRelation.Correctors
