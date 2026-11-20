import Mathlib.Probability.Martingale.OptionalStopping

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

end EinsteinFull.External.DFGW
