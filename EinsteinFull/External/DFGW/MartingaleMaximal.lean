import Mathlib.Probability.Martingale.OptionalStopping
import EinsteinFull.External.DFGW.IntegralCauchy

/-! # A discrete martingale maximal estimate

Doob's inequality applied to the absolute value bounds the probability of a large martingale
excursion by the first absolute moment of its terminal value.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
variable {ℱ : Filtration ℕ (inferInstance : MeasurableSpace Ω)}

/-- A discrete martingale's maximal excursion is controlled by its terminal absolute moment. -/
theorem measureReal_martingale_max_le (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ P)
    (n : ℕ) {ε : ℝ} (hε : 0 ≤ ε) :
    ε * P.real {ω | ∃ k ≤ n, ε ≤ |M k ω|} ≤ ∫ ω, |M n ω| ∂P := by
  let B : ℕ → Ω → ℝ := fun k ω => |M k ω|
  have hB : Submartingale B ℱ P := by
    have h := hM.submartingale.sup hM.neg.submartingale
    convert h using 1
    ext k ω
    simp [B, abs_eq_max_neg]
  have hBnonneg : 0 ≤ B := fun _ _ => abs_nonneg _
  let q : ℝ≥0 := ⟨ε, hε⟩
  let A : Set Ω := {ω | (q : ℝ) ≤
    (Finset.range (n + 1)).sup' (Finset.nonempty_range_add_one) (fun k => B k ω)}
  have hA : A = {ω | ∃ k ≤ n, ε ≤ |M k ω|} := by
    ext ω
    simp only [A, B, Finset.le_sup'_iff, Finset.mem_range, Nat.lt_succ_iff, q]
    rfl
  have hmax := maximal_ineq hB hBnonneg (ε := q) n
  have hi : Integrable (B n) P := hB.integrable n
  have hbound : (∫ ω in A, B n ω ∂P) ≤ ∫ ω, B n ω ∂P :=
    setIntegral_le_integral hi (ae_of_all P fun ω => abs_nonneg _)
  have hh : (q : ℝ≥0∞) * P A ≤ ENNReal.ofReal (∫ ω, B n ω ∂P) :=
    hmax.trans (ENNReal.ofReal_le_ofReal hbound)
  have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hh
  rw [ENNReal.toReal_mul, ENNReal.coe_toReal, ENNReal.toReal_ofReal
    (integral_nonneg fun ω => abs_nonneg _)] at ht
  change ε * P.real A ≤ ∫ ω, |M n ω| ∂P at ht
  simpa only [hA] using ht

/-- The squared excursion probability is bounded by the terminal second moment. -/
theorem sq_measureReal_martingale_max_le [IsProbabilityMeasure P]
    (M : ℕ → Ω → ℝ) (hM : Martingale M ℱ P) (n : ℕ) (hM2 : MemLp (M n) 2 P)
    {ε : ℝ} (hε : 0 ≤ ε) :
    (ε * P.real {ω | ∃ k ≤ n, ε ≤ |M k ω|}) ^ 2 ≤ ∫ ω, (M n ω) ^ 2 ∂P := by
  have hm := measureReal_martingale_max_le M hM n hε
  have hc := integral_mul_sq_le (fun ω => |M n ω|) (fun _ => 1) hM2.abs (memLp_const 1)
  simp only [mul_one, one_pow, integral_const, smul_eq_mul] at hc
  have htotal : P.real Set.univ = 1 := by simp [Measure.real]
  have hc' : (∫ ω, |M n ω| ∂P) ^ 2 ≤ ∫ ω, (M n ω) ^ 2 ∂P := by
    simpa only [sq_abs, htotal, mul_one] using hc
  have hp : 0 ≤ ε * P.real {ω | ∃ k ≤ n, ε ≤ |M k ω|} :=
    mul_nonneg hε measureReal_nonneg
  nlinarith

end EinsteinFull.External.DFGW
