import EinsteinFull.Calculus.C16SourceExponentialMaxAssembly

/-!
# Uniform exponential moments from tail bounds

A geometric decomposition turns a uniform exponential tail into an explicit
uniform exponential-moment bound.
-/

open MeasureTheory EinsteinRelation
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- An exponential tail yields both integrability and an explicit moment bound. -/
theorem exponential_moment_le_of_tail {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (S : Ω → ℝ) (hS : Measurable S) (hS0 : ∀ ω, 0 ≤ S ω)
    (K κ a : ℝ) (hK : 0 ≤ K) (ha : 0 < a) (hκ : a < κ)
    (htail : ∀ s : ℝ, 0 ≤ s → P.real {ω | s ≤ S ω} ≤ K * Real.exp (-(κ * s))) :
    Integrable (fun ω => Real.exp (a * S ω)) P ∧
      (∫ ω, Real.exp (a * S ω) ∂P) ≤ K * Real.exp a / (1 - Real.exp (a - κ)) := by
  have hi := EinsteinFull.c16_max_integrable_of_tail hS hS0 hK ha hκ htail
  refine ⟨hi, ?_⟩
  have hsets (n : ℕ) : MeasurableSet {ω | (n : ℝ) ≤ S ω} := measurableSet_le measurable_const hS
  have key : ∀ ω, ENNReal.ofReal (Real.exp (a * S ω)) ≤ ∑' n : ℕ,
      ENNReal.ofReal (Real.exp (a * ((n : ℝ) + 1))) *
        {ω | (n : ℝ) ≤ S ω}.indicator (1 : Ω → ℝ≥0∞) ω := by
    intro ω
    refine le_trans ?_ (ENNReal.le_tsum ⌊S ω⌋₊)
    have hmem : ω ∈ {ω' | ((⌊S ω⌋₊ : ℕ) : ℝ) ≤ S ω'} := Nat.floor_le (hS0 ω)
    rw [Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left (Nat.lt_floor_add_one (S ω)).le ha.le))
  have hlin : (∫⁻ ω, ENNReal.ofReal (Real.exp (a * S ω)) ∂P) ≤
      ∑' n : ℕ, ENNReal.ofReal (Real.exp (a * ((n : ℝ) + 1))) *
        P {ω | (n : ℝ) ≤ S ω} := by
    refine (lintegral_mono key).trans ?_
    rw [lintegral_tsum fun n => ((measurable_one.indicator (hsets n)).const_mul _).aemeasurable]
    refine le_of_eq (tsum_congr fun n => ?_)
    rw [lintegral_const_mul _ (measurable_one.indicator (hsets n)),
      lintegral_indicator_one (hsets n)]
  have hterm (n : ℕ) : ENNReal.ofReal (Real.exp (a * ((n : ℝ) + 1))) *
      P {ω | (n : ℝ) ≤ S ω} ≤ ENNReal.ofReal ((K * Real.exp a) *
        Real.exp (a - κ) ^ n) := by
    rw [← ofReal_measureReal (measure_ne_top P _), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    refine ENNReal.ofReal_le_ofReal ?_
    have h1 := mul_le_mul_of_nonneg_left (htail n n.cast_nonneg) (Real.exp_pos (a * ((n : ℝ) + 1))).le
    refine h1.trans (le_of_eq ?_)
    calc Real.exp (a * ((n : ℝ) + 1)) * (K * Real.exp (-(κ * n))) =
          K * (Real.exp (a * ((n : ℝ) + 1)) * Real.exp (-(κ * n))) := by ring
      _ = K * (Real.exp a * Real.exp (n * (a - κ))) := by
          rw [← Real.exp_add, ← Real.exp_add]; congr 2; ring
      _ = _ := by rw [Real.exp_nat_mul]; ring
  have hsum : Summable (fun n : ℕ => (K * Real.exp a) * Real.exp (a - κ) ^ n) :=
    (summable_geometric_of_lt_one (Real.exp_pos _).le
      (by rw [Real.exp_lt_one_iff]; linarith)).mul_left _
  have hbound : (∫⁻ ω, ENNReal.ofReal (Real.exp (a * S ω)) ∂P) ≤
      ENNReal.ofReal (∑' n : ℕ, (K * Real.exp a) * Real.exp (a - κ) ^ n) := by
    calc
      _ ≤ _ := hlin
      _ ≤ ∑' n : ℕ, ENNReal.ofReal ((K * Real.exp a) * Real.exp (a - κ) ^ n) :=
        ENNReal.tsum_le_tsum hterm
      _ = _ := (ENNReal.ofReal_tsum_of_nonneg
        (fun n => mul_nonneg (mul_nonneg hK (Real.exp_pos _).le)
          (pow_nonneg (Real.exp_pos _).le n)) hsum).symm
  have hsum_eq : (∑' n : ℕ, (K * Real.exp a) * Real.exp (a - κ) ^ n) =
      K * Real.exp a / (1 - Real.exp (a - κ)) := by
    rw [tsum_mul_left, tsum_geometric_of_lt_one (Real.exp_pos _).le
      (by rw [Real.exp_lt_one_iff]; linarith)]
    exact (div_eq_mul_inv _ _).symm
  rw [← ofReal_integral_eq_lintegral_ofReal hi
    (Filter.Eventually.of_forall fun ω => (Real.exp_pos _).le), hsum_eq] at hbound
  have hpos : 0 ≤ K * Real.exp a / (1 - Real.exp (a - κ)) := by
    apply div_nonneg (mul_nonneg hK (Real.exp_pos _).le)
    have : Real.exp (a - κ) < 1 := by rw [Real.exp_lt_one_iff]; linarith
    linarith
  exact (ENNReal.ofReal_le_ofReal_iff hpos).mp hbound

end EinsteinFull.Regeneration
