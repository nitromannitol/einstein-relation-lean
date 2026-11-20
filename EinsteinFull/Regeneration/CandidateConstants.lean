import EinsteinFull.Regeneration.CoupledCandidateMoment

/-!
# Uniform constants for the candidate searches of the split coupling

For a small exponent, the first round of a candidate search has a uniformly bounded
exponential moment and a failed coin followed by a new round has weight uniformly
below one, at almost every grid endpoint of every split coupling.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration
open EinsteinRelation.External.GantertSection7Support
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

attribute [local irreducible] firstRoundedCandidate roundedCandidateSequence passageSequence
  firstSuccessfulCandidate

/-- A smaller tilt of the first-candidate weight is at most one plus a multiple of the
larger tilt. -/
theorem firstCandidateWeight_le_tilt {d : ℕ} (Δ : ℝ≥0) (lam R L a b : ℝ) (ha : 0 ≤ a)
    (hab : a ≤ b) (hb : 0 < b) (i : Fin d) (γ : Path d) :
    firstCandidateWeight Δ lam R L a i γ ≤
      1 + ENNReal.ofReal (a / b) * firstCandidateWeight Δ lam R L b i γ := by
  by_cases hC : firstRoundedCandidate Δ lam R L γ i ≠ ⊤
  · simp only [firstCandidateWeight]
    rw [Set.indicator_of_mem (show γ ∈ {γ : Path d | firstRoundedCandidate Δ lam R L γ i ≠ ⊤}
        from hC), Set.indicator_of_mem (show γ ∈ {γ : Path d |
        firstRoundedCandidate Δ lam R L γ i ≠ ⊤} from hC),
      ← ENNReal.ofReal_mul (div_nonneg ha hb.le), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (mul_nonneg (div_nonneg ha hb.le) (Real.exp_pos _).le)]
    apply ENNReal.ofReal_le_ofReal
    set X := lam * (γ (firstRoundedCandidate Δ lam R L γ i).toNNReal i - γ 0 i - L / lam)
    have h := exp_mul_le_one_add_mul_exp (a / b) (b * X) (div_nonneg ha hb.le)
      ((div_le_one hb).mpr hab)
    have heq : a / b * (b * X) = a * X := by field_simp
    rw [heq] at h
    calc Real.exp (a * lam * (γ (firstRoundedCandidate Δ lam R L γ i).toNNReal i - γ 0 i - L / lam))
        = Real.exp (a * X) := by congr 1; ring
      _ ≤ 1 + a / b * Real.exp (b * X) := h
      _ = 1 + a / b * Real.exp (b * lam *
          (γ (firstRoundedCandidate Δ lam R L γ i).toNNReal i - γ 0 i - L / lam)) := by
          congr 3; ring
  · simp only [firstCandidateWeight]
    rw [Set.indicator_of_notMem (show γ ∉ {γ : Path d | firstRoundedCandidate Δ lam R L γ i ≠ ⊤}
      from hC)]
    exact zero_le

/-- The squared restart weight is a tilt of the first-candidate weight at level `3R`. -/
theorem squaredRestartWeight_le_tilt {d : ℕ} (Δ : ℝ≥0) (lam R a b : ℝ) (hlam : 0 < lam)
    (ha : 0 ≤ a) (hab : 2 * a ≤ b) (hb : 0 < b) (i : Fin d) (γ : Path d) :
    squaredRestartWeight Δ lam R a i γ ≤ ENNReal.ofReal (Real.exp (6 * a * (lam * R))) *
      (1 + ENNReal.ofReal (2 * a / b) * firstCandidateWeight Δ lam R (3 * lam * R) b i γ) := by
  by_cases hC : firstRoundedCandidate Δ lam R (3 * lam * R) γ i ≠ ⊤
  · simp only [squaredRestartWeight, firstCandidateWeight]
    rw [Set.indicator_of_mem (show γ ∈ {γ : Path d |
        firstRoundedCandidate Δ lam R (3 * lam * R) γ i ≠ ⊤} from hC),
      Set.indicator_of_mem (show γ ∈ {γ : Path d |
        firstRoundedCandidate Δ lam R (3 * lam * R) γ i ≠ ⊤} from hC),
      ← ENNReal.ofReal_mul (div_nonneg (by linarith) hb.le), ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_add zero_le_one (mul_nonneg (div_nonneg (by linarith) hb.le)
        (Real.exp_pos _).le), ← ENNReal.ofReal_mul (Real.exp_pos _).le]
    apply ENNReal.ofReal_le_ofReal
    set Y := lam * (γ (firstRoundedCandidate Δ lam R (3 * lam * R) γ i).toNNReal i - γ 0 i -
      3 * lam * R / lam)
    have h := exp_mul_le_one_add_mul_exp (2 * a / b) (b * Y) (div_nonneg (by linarith) hb.le)
      ((div_le_one hb).mpr hab)
    have heq : 2 * a / b * (b * Y) = 2 * a * Y := by field_simp
    rw [heq] at h
    have hsplit : 2 * (a * lam * (γ (firstRoundedCandidate Δ lam R (3 * lam * R) γ i).toNNReal i -
        γ 0 i)) = 6 * a * (lam * R) + 2 * a * Y := by
      simp only [Y]
      field_simp
      ring
    rw [hsplit, Real.exp_add]
    apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
    calc Real.exp (2 * a * Y) ≤ 1 + 2 * a / b * Real.exp (b * Y) := h
      _ = _ := by congr 3; ring
  · simp only [squaredRestartWeight]
    rw [Set.indicator_of_notMem (show γ ∉ {γ : Path d |
      firstRoundedCandidate Δ lam R (3 * lam * R) γ i ≠ ⊤} from hC)]
    exact zero_le

end EinsteinFull.Regeneration
