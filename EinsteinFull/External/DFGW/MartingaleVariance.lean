import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.PullOut
import Mathlib.MeasureTheory.Function.L2Space

/-! # Variance of square-integrable martingale increments

Orthogonality gives the variance identity for a square-integrable martingale and its
increments. In discrete time, equal increment variances yield linear variance growth.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace EinsteinFull.External.DFGW

variable {Ω ι : Type*} [Preorder ι] {m : MeasurableSpace Ω}
variable {ℱ : Filtration ι m} {P : Measure Ω} [IsFiniteMeasure P]
variable {M : ι → Ω → ℝ}

/-- A martingale value is orthogonal to every later square-integrable increment. -/
theorem integral_martingale_mul_increment (hM : Martingale M ℱ P)
    {s t : ι} (hst : s ≤ t) (hs : MemLp (M s) 2 P) (ht : MemLp (M t) 2 P) :
    ∫ ω, M s ω * (M t ω - M s ω) ∂P = 0 := by
  have hsint := hs.integrable (by norm_num)
  have htint := ht.integrable (by norm_num)
  have hinc : Integrable (M t - M s) P := htint.sub hsint
  have hprod : Integrable (M s * (M t - M s)) P := hs.integrable_mul (ht.sub hs)
  have hzero : P[M t - M s | ℱ s] =ᵐ[P] 0 := by
    have hc := condExp_of_stronglyMeasurable (ℱ.le s) (hM.stronglyAdapted s) hsint
    filter_upwards [condExp_sub htint hsint (ℱ s), hM.2 s t hst] with ω ha hb
    simp only [Pi.sub_apply, Pi.zero_apply] at ha ⊢
    rw [ha, hb, hc, sub_self]
  have hpull := condExp_mul_of_stronglyMeasurable_left (hM.stronglyAdapted s) hprod hinc
  calc
    (∫ ω, M s ω * (M t ω - M s ω) ∂P) =
        ∫ ω, P[M s * (M t - M s) | ℱ s] ω ∂P := by
      simpa only [Pi.mul_apply, Pi.sub_apply] using
        (integral_condExp (μ := P) (f := M s * (M t - M s)) (ℱ.le s)).symm
    _ = 0 := by
      apply integral_eq_zero_of_ae
      filter_upwards [hpull, hzero] with ω hp hz
      simp only [Pi.mul_apply, Pi.zero_apply] at hp hz
      change P[M s * (M t - M s) | ℱ s] ω = (0 : ℝ)
      rw [hp, hz, mul_zero]

/-- The variance of a martingale increment is the difference of the second moments. -/
theorem integral_martingale_increment_sq (hM : Martingale M ℱ P)
    {s t : ι} (hst : s ≤ t) (hs : MemLp (M s) 2 P) (ht : MemLp (M t) 2 P) :
    (∫ ω, (M t ω - M s ω) ^ 2 ∂P) =
      (∫ ω, M t ω ^ 2 ∂P) - ∫ ω, M s ω ^ 2 ∂P := by
  have hinc : MemLp (M t - M s) 2 P := ht.sub hs
  have hprod : Integrable (M s * (M t - M s)) P := hs.integrable_mul hinc
  have hortho := integral_martingale_mul_increment hM hst hs ht
  have heq : (fun ω => M t ω ^ 2) =
      (fun ω => M s ω ^ 2) + (fun ω => (M t ω - M s ω) ^ 2) +
        (fun ω => 2 * (M s ω * (M t ω - M s ω))) := by
    funext ω
    simp only [Pi.add_apply]
    ring
  have hi := congrArg (fun z : Ω → ℝ => ∫ ω, z ω ∂P) heq
  simp only [Pi.add_apply] at hi
  have hincsq : Integrable (fun ω => (M t ω - M s ω) ^ 2) P := by
    simpa only [Pi.sub_apply] using hinc.integrable_sq
  have hcross : Integrable (fun ω => 2 * (M s ω * (M t ω - M s ω))) P := by
    simpa only [Pi.mul_apply, Pi.sub_apply] using hprod.const_mul 2
  have hleft : Integrable (fun ω => M s ω ^ 2 + (M t ω - M s ω) ^ 2) P :=
    hs.integrable_sq.add hincsq
  rw [integral_add hleft hcross, integral_add hs.integrable_sq hincsq,
    integral_const_mul, hortho] at hi
  linarith

/-- Equal second moments of discrete increments give linear growth of second moments. -/
theorem integral_martingale_sq_of_stationary_increments {ℱ : Filtration ℕ m}
    {M : ℕ → Ω → ℝ} (hM : Martingale M ℱ P) (hL2 : ∀ n, MemLp (M n) 2 P)
    (hzero : M 0 =ᵐ[P] 0)
    (hstationary : ∀ k, (∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂P) =
      ∫ ω, (M 1 ω - M 0 ω) ^ 2 ∂P) (n : ℕ) :
    (∫ ω, M n ω ^ 2 ∂P) = (n : ℝ) * ∫ ω, M 1 ω ^ 2 ∂P := by
  have hsum : (∑ k ∈ Finset.range n, ∫ ω, (M (k + 1) ω - M k ω) ^ 2 ∂P) =
      (∫ ω, M n ω ^ 2 ∂P) - ∫ ω, M 0 ω ^ 2 ∂P := by
    simp_rw [integral_martingale_increment_sq hM (Nat.le_succ _) (hL2 _) (hL2 _)]
    exact Finset.sum_range_sub (fun j => ∫ ω, M j ω ^ 2 ∂P) n
  have hz : (∫ ω, M 0 ω ^ 2 ∂P) = 0 := by
    apply integral_eq_zero_of_ae
    filter_upwards [hzero] with ω hω
    simp only [Pi.zero_apply] at hω
    rw [hω]
    norm_num
  have hone : (∫ ω, (M 1 ω - M 0 ω) ^ 2 ∂P) = ∫ ω, M 1 ω ^ 2 ∂P := by
    apply integral_congr_ae
    filter_upwards [hzero] with ω hω
    simp only [Pi.zero_apply, hω, sub_zero]
  simp_rw [hstationary, hone] at hsum
  simpa only [Finset.sum_const_zero, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    hz, sub_zero] using hsum.symm

end EinsteinFull.External.DFGW
