import Mathlib.Probability.Moments.Variance

/-!
# Variance contraction for a finite family

A finite family of random variables with equal variance has a strictly smaller
variance after averaging if one pair is independent. This is the covariance
counting step in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Lemma 2.13.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

/-- The covariance of two square-integrable variables is at most the arithmetic
mean of their variances. -/
theorem covariance_le_average_variance {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) :
    ProbabilityTheory.covariance X Y P ≤
      (ProbabilityTheory.variance X P + ProbabilityTheory.variance Y P) / 2 := by
  have h := ProbabilityTheory.variance_nonneg (X - Y) P
  rw [ProbabilityTheory.variance_sub hX hY] at h
  linarith

/-- One independent pair yields a strict gain over the variance bound for a
finite sum of equal-variance variables. -/
theorem variance_sum_le_of_independent_pair {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (V : ℝ)
    (hV : ∀ i, ProbabilityTheory.variance (X i) P = V)
    (i₀ j₀ : ι) (hij : ProbabilityTheory.IndepFun (X i₀) (X j₀) P) :
    ProbabilityTheory.variance (∑ i, X i) P ≤ ((Fintype.card ι : ℝ) ^ 2 - 1) * V := by
  classical
  have hcov (i j : ι) : ProbabilityTheory.covariance (X i) (X j) P ≤ V := by
    have h := covariance_le_average_variance P (hX i) (hX j)
    rw [hV i, hV j] at h
    linarith
  have hzero : ProbabilityTheory.covariance (X i₀) (X j₀) P = 0 :=
    hij.covariance_eq_zero (hX i₀) (hX j₀)
  rw [ProbabilityTheory.variance_sum hX]
  calc
    _ ≤ ∑ i : ι, ∑ j : ι, (V - if i = i₀ ∧ j = j₀ then V else 0) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        rw [hzero]
        simp
      · simpa using hcov i j
    _ = ((Fintype.card ι : ℝ) ^ 2 - 1) * V := by
      simp only [Finset.sum_sub_distrib, Finset.sum_const,
        Finset.card_univ, nsmul_eq_mul]
      have hi (i : ι) : (∑ j : ι, if i = i₀ ∧ j = j₀ then V else 0) =
          if i = i₀ then V else 0 := by
        by_cases h : i = i₀ <;> simp [h]
      simp_rw [hi]
      simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true]
      ring

/-- Averaging a finite equal-variance family with an independent pair contracts
its variance by an explicit positive fraction. -/
theorem variance_average_le_of_independent_pair {Ω ι : Type*} [MeasurableSpace Ω]
    [Fintype ι] (P : Measure Ω) [IsProbabilityMeasure P] (X : ι → Ω → ℝ)
    (hX : ∀ i, MemLp (X i) 2 P) (V : ℝ)
    (hV : ∀ i, ProbabilityTheory.variance (X i) P = V)
    (i₀ j₀ : ι) (hij : ProbabilityTheory.IndepFun (X i₀) (X j₀) P) :
    ProbabilityTheory.variance ((Fintype.card ι : ℝ)⁻¹ • (∑ i, X i)) P ≤
      (1 - (Fintype.card ι : ℝ)⁻¹ ^ 2) * V := by
  letI : Nonempty ι := ⟨i₀⟩
  have hn : (Fintype.card ι : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [ProbabilityTheory.variance_smul]
  calc
    _ ≤ (Fintype.card ι : ℝ)⁻¹ ^ 2 * (((Fintype.card ι : ℝ) ^ 2 - 1) * V) :=
      mul_le_mul_of_nonneg_left (variance_sum_le_of_independent_pair P X hX V hV i₀ j₀ hij)
        (sq_nonneg _)
    _ = _ := by field_simp

/-- A weighted variance triangle inequality, with an adjustable coefficient on
both terms. -/
theorem variance_add_le_weighted {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (δ : ℝ) (hδ : 0 < δ) :
    ProbabilityTheory.variance (X + Y) P ≤
      (1 + δ) * ProbabilityTheory.variance X P +
        (1 + δ⁻¹) * ProbabilityTheory.variance Y P := by
  have hn := ProbabilityTheory.variance_nonneg (δ • X - Y) P
  rw [ProbabilityTheory.variance_sub (hX.const_smul δ) hY,
    ProbabilityTheory.variance_smul, ProbabilityTheory.covariance_smul_left] at hn
  rw [ProbabilityTheory.variance_add hX hY]
  have hi : 0 ≤ δ⁻¹ := inv_nonneg.mpr hδ.le
  have hmul := mul_nonneg hi hn
  have hmul' : 0 ≤ δ * ProbabilityTheory.variance X P -
      2 * ProbabilityTheory.covariance X Y P + δ⁻¹ * ProbabilityTheory.variance Y P := by
    calc
      0 ≤ δ⁻¹ * (δ ^ 2 * ProbabilityTheory.variance X P -
          2 * (δ * ProbabilityTheory.covariance X Y P) + ProbabilityTheory.variance Y P) := hmul
      _ = _ := by field_simp
  linarith

/-- An additive error preserves a strict variance contraction, at the cost of
an explicit multiple of its variance. -/
theorem variance_add_le_of_contracting {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {X Y : Ω → ℝ}
    (hX : MemLp X 2 P) (hY : MemLp Y 2 P) (t V B : ℝ)
    (ht1 : t < 1) (hV : 0 ≤ V)
    (hXbound : ProbabilityTheory.variance X P ≤ t * V)
    (hYbound : ProbabilityTheory.variance Y P ≤ B) :
    ProbabilityTheory.variance (X + Y) P ≤
      ((1 + t) / 2) * V + (1 + 2 / (1 - t)) * B := by
  let δ := (1 - t) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hδinv : δ⁻¹ = 2 / (1 - t) := by
    dsimp [δ]
    field_simp
  have hfactor : (1 + δ) * t ≤ (1 + t) / 2 := by
    dsimp [δ]
    nlinarith [sq_nonneg (1 - t)]
  calc
    _ ≤ (1 + δ) * ProbabilityTheory.variance X P +
        (1 + δ⁻¹) * ProbabilityTheory.variance Y P :=
      variance_add_le_weighted P hX hY δ hδ
    _ ≤ (1 + δ) * (t * V) + (1 + δ⁻¹) * B :=
      add_le_add (mul_le_mul_of_nonneg_left hXbound (by linarith))
        (mul_le_mul_of_nonneg_left hYbound (by positivity))
    _ ≤ _ := by
      rw [hδinv]
      have hm := mul_le_mul_of_nonneg_right hfactor hV
      nlinarith

end EinsteinFull.Homogenization
