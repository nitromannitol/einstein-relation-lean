import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

open MeasureTheory Filter Set
open scoped Topology

namespace EinsteinFull.Calculus

/-- A nonnegative subprobability row that concentrates near the pole acts as an
approximate identity on bounded continuous scalar functions. The measure can be
Lebesgue measure restricted to a ball, and the limit is from positive times. -/
theorem br14_local_mass_approximate_identity
    {X : Type*} [MetricSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) (q : ℝ → X → ℝ) (y : X) (f : X → ℝ)
    (hf : Continuous f) (B : ℝ) (hB : ∀ x, |f x| ≤ B)
    (hqint : ∀ t > 0, Integrable (q t) μ)
    (hqnonneg : ∀ t > 0, ∀ x, 0 ≤ q t x)
    (hqmass : ∀ t > 0, (∫ x, q t x ∂μ) ≤ 1)
    (r₀ : ℝ) (hr₀ : 0 < r₀)
    (hlocal : ∀ r > 0, r < r₀ → Tendsto (fun t : ℝ => ∫ x in Metric.ball y r, q t x ∂μ)
      (𝓝[>] 0) (𝓝 1)) :
    Tendsto (fun t : ℝ => ∫ x, q t x * f x ∂μ) (𝓝[>] 0) (𝓝 (f y)) := by
  have hB0 : 0 ≤ B := (abs_nonneg (f y)).trans (hB y)
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : 0 < ε / (4 * (B + 1)) := by positivity
  obtain ⟨r, hr, hosc⟩ := (Metric.continuousAt_iff.mp hf.continuousAt) (ε / 4) (by positivity)
  let r' := min r (r₀ / 2)
  have hr' : 0 < r' := lt_min hr (by positivity)
  have hr'₀ : r' < r₀ := lt_of_le_of_lt (min_le_right _ _) (by linarith)
  have hnear := (Metric.tendsto_nhds.mp (hlocal r' hr' hr'₀)) _ hδ
  filter_upwards [self_mem_nhdsWithin, hnear] with t ht hnear
  have ht0 : 0 < t := ht
  let S := Metric.ball y r'
  have hS : MeasurableSet S := Metric.isOpen_ball.measurableSet
  have hq := hqint t ht0
  have hp : Integrable (fun x => q t x * f x) μ :=
    hq.mul_bdd hf.aestronglyMeasurable (ae_of_all _ fun x => by simpa [Real.norm_eq_abs] using hB x)
  have hd : Integrable (fun x => q t x * (f x - f y)) μ := by
    convert hp.sub (hq.mul_const (f y)) using 1
    ext x
    simp only [Pi.sub_apply]
    ring
  have hlocalmass : 1 - ε / (4 * (B + 1)) < ∫ x in S, q t x ∂μ := by
    have : |(∫ x in S, q t x ∂μ) - 1| < ε / (4 * (B + 1)) := by
      simpa [S, Real.dist_eq] using hnear
    exact (abs_lt.mp this).1 |> fun h => by linarith
  have htotal0 : 0 ≤ ∫ x, q t x ∂μ := integral_nonneg fun x => hqnonneg t ht0 x
  have htotal := hqmass t ht0
  have hout : 0 ≤ ∫ x in Sᶜ, q t x ∂μ := integral_nonneg fun x => hqnonneg t ht0 x
  have hsplit := integral_add_compl hS hq
  have hinside : (∫ x in S, |q t x * (f x - f y)| ∂μ) ≤
      (ε / 4) * ∫ x in S, q t x ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hd.norm.restrict (hq.restrict.const_mul _)
    filter_upwards [ae_restrict_mem hS] with x hx
    have hfx : |f x - f y| < ε / 4 := by
      have hx' : dist x y < r' := by simpa [S, Metric.mem_ball] using hx
      have := hosc (lt_of_lt_of_le hx' (min_le_left _ _))
      simpa [Real.dist_eq] using this
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hqnonneg t ht0 x)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hfx.le (hqnonneg t ht0 x)
  have houtside : (∫ x in Sᶜ, |q t x * (f x - f y)| ∂μ) ≤
      (2 * B) * ∫ x in Sᶜ, q t x ∂μ := by
    rw [← integral_const_mul]
    apply integral_mono_ae hd.norm.restrict (hq.restrict.const_mul _)
    filter_upwards [] with x
    have hfxy : |f x - f y| ≤ 2 * B := by
      calc
        |f x - f y| ≤ |f x| + |f y| := abs_sub _ _
        _ ≤ 2 * B := by linarith [hB x, hB y]
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hqnonneg t ht0 x)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hfxy (hqnonneg t ht0 x)
  have hbound : |∫ x, q t x * (f x - f y) ∂μ| ≤
      (ε / 4) * (∫ x in S, q t x ∂μ) + (2 * B) * (∫ x in Sᶜ, q t x ∂μ) := by
    calc
      _ ≤ ∫ x, |q t x * (f x - f y)| ∂μ := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun x => q t x * (f x - f y))
      _ = (∫ x in S, |q t x * (f x - f y)| ∂μ) +
          (∫ x in Sᶜ, |q t x * (f x - f y)| ∂μ) := by
        simpa [Real.norm_eq_abs] using (integral_add_compl hS hd.norm).symm
      _ ≤ _ := add_le_add hinside houtside
  have hinside0 : 0 ≤ ∫ x in S, q t x ∂μ := integral_nonneg fun x => hqnonneg t ht0 x
  have hinside1 : (∫ x in S, q t x ∂μ) ≤ 1 := by linarith
  have houtsmall : (∫ x in Sᶜ, q t x ∂μ) < ε / (4 * (B + 1)) := by linarith
  have hdeficit : 0 ≤ 1 - ∫ x, q t x ∂μ := by linarith
  have hdefsmall : 1 - (∫ x, q t x ∂μ) < ε / (4 * (B + 1)) := by linarith
  have hδcalc : (B + 1) * (ε / (4 * (B + 1))) = ε / 4 := by field_simp
  have hnormsmall : |∫ x, q t x * (f x - f y) ∂μ| < 3 * ε / 4 := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ ε / 4) (sub_nonneg.mpr hinside1),
      mul_nonneg (by positivity : 0 ≤ 2 * B) (sub_nonneg.mpr (le_of_lt houtsmall))]
  have hmissing : |f y * ((∫ x, q t x ∂μ) - 1)| < ε / 4 := by
    rw [abs_mul, abs_of_nonpos (by linarith : (∫ x, q t x ∂μ) - 1 ≤ 0)]
    have := hB y
    nlinarith [mul_nonneg (sub_nonneg.mpr (hB y)) hdeficit, mul_nonneg hB0 (sub_nonneg.mpr (le_of_lt hdefsmall))]
  have hid : (∫ x, q t x * f x ∂μ) - f y =
      (∫ x, q t x * (f x - f y) ∂μ) + f y * ((∫ x, q t x ∂μ) - 1) := by
    rw [show (fun x => q t x * (f x - f y)) =
      (fun x => q t x * f x - q t x * f y) by funext x; ring,
      integral_sub hp (hq.mul_const _), integral_mul_const]
    ring
  rw [Real.dist_eq, hid]
  exact lt_of_le_of_lt (abs_add_le _ _) (by linarith)

#print axioms br14_local_mass_approximate_identity

end EinsteinFull.Calculus
