import EinsteinFull.Regeneration.ExponentialTailMoment

/-!
# Exponential moments from geometric tails

A geometric bound at nonnegative integer levels controls an exponential
moment of a nonnegative random variable.
-/

open MeasureTheory Set
open scoped ENNReal

namespace EinsteinFull.Regeneration

/-- Integer geometric tails give a uniform exponential moment. -/
theorem exponential_moment_le_of_geometric_tail {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (S : Ω → ℝ) (hS : Measurable S)
    (hS0 : ∀ ω, 0 ≤ S ω) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ < 1)
    (htail : ∀ n : ℕ, P {ω | (n : ℝ) < S ω} ≤ ENNReal.ofReal (1 - δ) ^ n) :
    Integrable (fun ω => Real.exp ((δ / 4) * S ω)) P ∧
      (∫ ω, Real.exp ((δ / 4) * S ω) ∂P) ≤
        Real.exp δ * Real.exp (δ / 4) / (1 - Real.exp (δ / 4 - δ / 2)) := by
  apply exponential_moment_le_of_tail P S hS hS0 (Real.exp δ) (δ / 2) (δ / 4)
    (Real.exp_pos δ).le (by positivity) (by linarith)
  intro s hs
  by_cases hz : s = 0
  · subst s
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
    exact (measureReal_le_one : P.real {ω | (0 : ℝ) ≤ S ω} ≤ 1).trans
      (Real.one_le_exp hδ.le)
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hz)
    let n : ℕ := ⌊s / 2⌋₊
    have hnle : (n : ℝ) ≤ s / 2 := Nat.floor_le (by positivity)
    have hns : (n : ℝ) < s := by linarith
    have hsub : {ω | s ≤ S ω} ⊆ {ω | (n : ℝ) < S ω} :=
      fun _ hω => hns.trans_le hω
    have hbound := (measure_mono hsub).trans (htail n)
    have hreal := ENNReal.toReal_mono (by finiteness) hbound
    have hq : 0 ≤ 1 - δ := by linarith
    rw [← ENNReal.ofReal_pow hq, ENNReal.toReal_ofReal (pow_nonneg hq n)] at hreal
    have hqexp : 1 - δ ≤ Real.exp (-δ) := by
      have h := Real.add_one_le_exp (-δ)
      linarith
    have hpow : (1 - δ) ^ n ≤ Real.exp (-δ * n) := by
      calc
        (1 - δ) ^ n ≤ Real.exp (-δ) ^ n := pow_le_pow_left₀ hq hqexp n
        _ = Real.exp (-δ * n) := by rw [mul_comm (-δ) (n : ℝ), Real.exp_nat_mul]
    have hfloor := Nat.lt_floor_add_one (s / 2)
    have hexp : Real.exp (-δ * n) ≤ Real.exp δ * Real.exp (-(δ / 2 * s)) := by
      rw [← Real.exp_add]
      apply Real.exp_le_exp.mpr
      change s / 2 < (n : ℝ) + 1 at hfloor
      nlinarith
    exact hreal.trans (hpow.trans hexp)

end EinsteinFull.Regeneration
