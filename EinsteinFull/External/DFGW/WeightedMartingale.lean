import Mathlib.Probability.Martingale.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

/-! # Deterministically weighted martingale increments

A finite sum of deterministic weights times martingale increments remains a martingale.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
variable {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}

/-- Deterministically weighted partial sums of discrete martingale increments form a martingale. -/
theorem martingale_sum_weighted_increments (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ P)
    (w : ℕ → ℝ) :
    Martingale (fun n ω => ∑ k ∈ Finset.range n, w k * (M (k + 1) ω - M k ω)) ℱ P := by
  let F : ℕ → Ω → ℝ := fun n ω => ∑ k ∈ Finset.range n, w k * (M (k + 1) ω - M k ω)
  have hadapt : StronglyAdapted ℱ F := by
    intro n
    change StronglyMeasurable[ℱ n] (fun ω => ∑ k ∈ Finset.range n, w k * (M (k + 1) ω - M k ω))
    apply Finset.stronglyMeasurable_fun_sum
    intro k hk
    have hkn : k + 1 ≤ n := Nat.succ_le_of_lt (Finset.mem_range.mp hk)
    have hkn' : k ≤ n := le_trans (Nat.le_succ k) hkn
    exact ((hM.stronglyMeasurable (k + 1)).mono (ℱ.mono hkn) |>.sub
      ((hM.stronglyMeasurable k).mono (ℱ.mono hkn'))).const_mul (w k)
  have hint (n : ℕ) : Integrable (F n) P := by
    apply integrable_finsetSum
    intro k hk
    exact ((hM.integrable (k + 1)).sub (hM.integrable k)).const_mul (w k)
  apply martingale_of_condExp_sub_eq_zero_nat hadapt hint
  intro n
  have heq : F (n + 1) - F n = (w n) • (M (n + 1) - M n) := by
    funext ω
    simp only [F, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_range_succ, add_sub_cancel_left]
  rw [heq]
  have hzero : P[M (n + 1) - M n | ℱ n] =ᵐ[P] 0 := by
    have hc := condExp_of_stronglyMeasurable (ℱ.le n) (hM.stronglyMeasurable n) (hM.integrable n)
    filter_upwards [condExp_sub (hM.integrable (n + 1)) (hM.integrable n) (ℱ n),
      hM.condExp_ae_eq (Nat.le_succ n)] with ω ha hb
    simp only [Pi.sub_apply, Pi.zero_apply] at ha ⊢
    rw [ha, hb, hc, sub_self]
  filter_upwards [condExp_smul (μ := P) (m := ℱ n) (w n) (M (n + 1) - M n), hzero] with ω ha hz
  simp only [Pi.smul_apply, Pi.zero_apply] at ha hz ⊢
  rw [ha, hz, smul_zero]

end EinsteinFull.External.DFGW
