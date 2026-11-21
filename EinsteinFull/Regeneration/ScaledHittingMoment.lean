import EinsteinFull.Regeneration.ExponentialTailMoment
import EinsteinFull.Regeneration.PassagesFromHitting

/-!
# Scaled hitting-time moments

A uniform exponential hitting-time bound gives a uniform exponential moment
for the scaled hitting time.
-/

open MeasureTheory
open scoped NNReal ENNReal

namespace EinsteinFull.Regeneration

/-- A scaled exponential tail controls the scaled hitting-time moment. -/
theorem scaled_time_exponential_moment_of_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : Ω → ℝ≥0∞) (hτ : Measurable τ)
    (m κ C b a : ℝ) (hm : 0 < m) (hC : 0 ≤ C)
    (ha : 0 < a) (haκ : a < κ / 2)
    (htail : ∀ t : ℝ, 0 ≤ t → μ {ω | ENNReal.ofReal t ≤ τ ω} ≤
      ENNReal.ofReal (C * Real.exp (-κ * m * t + b))) :
    Integrable (fun ω => Real.exp (a * (m * (τ ω).toReal))) μ ∧
      (∫ ω, Real.exp (a * (m * (τ ω).toReal)) ∂μ) ≤
        max 1 (C * Real.exp b) * Real.exp a / (1 - Real.exp (a - κ / 2)) := by
  apply exponential_moment_le_of_tail μ (fun ω => m * (τ ω).toReal)
    (measurable_const.mul hτ.ennreal_toReal)
    (fun _ => mul_nonneg hm.le ENNReal.toReal_nonneg)
    (max 1 (C * Real.exp b)) (κ / 2) a (by positivity) ha haκ
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    simpa only [mul_zero, neg_zero, Real.exp_zero, mul_one] using
      (measureReal_le_one : μ.real {ω | (0 : ℝ) ≤ m * (τ ω).toReal} ≤ 1).trans
        (le_max_left 1 (C * Real.exp b))
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hsub : {ω | s ≤ m * (τ ω).toReal} ⊆
        {ω | ENNReal.ofReal (s / (2 * m)) ≤ τ ω} := by
      intro ω hω
      change s ≤ m * (τ ω).toReal at hω
      have hfin : τ ω ≠ ⊤ := by
        intro ht
        rw [ht, ENNReal.toReal_top, mul_zero] at hω
        linarith
      have hlt : s / (2 * m) < (τ ω).toReal := by
        apply (div_lt_iff₀ (by positivity : 0 < 2 * m)).2
        nlinarith
      exact ((ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hfin).2 hlt).le
    have hbound := (measure_mono hsub).trans (htail (s / (2 * m)) (by positivity))
    have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hbound
    simp only [ENNReal.toReal_ofReal
      (mul_nonneg hC (Real.exp_pos _).le)] at hreal
    calc
      _ ≤ C * Real.exp (-κ * m * (s / (2 * m)) + b) := hreal
      _ = (C * Real.exp b) * Real.exp (-(κ / 2 * s)) := by
        have heq : -κ * m * (s / (2 * m)) + b = b + -(κ / 2 * s) := by
          field_simp
          ring
        rw [heq, Real.exp_add]
        ring
      _ ≤ max 1 (C * Real.exp b) * Real.exp (-(κ / 2 * s)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (Real.exp_pos _).le

/-- GMP's forward-hitting estimate gives a uniform moment at scale `1 / lam²`. -/
theorem scaled_first_hitting_moment {d : ℕ}
    (μ : Measure (EinsteinRelation.FieldPair d × EinsteinRelation.Regeneration.CoupledSample d))
    [IsProbabilityMeasure μ] (i : Fin d) (lam κ C b a : ℝ)
    (hlam : 0 < lam) (hC : 0 ≤ C) (hb : 0 ≤ b) (ha : 0 < a) (haκ : a < κ / 2)
    (hhit : ∀ (T : ℝ≥0) (level : ℝ), 0 ≤ level →
      μ {z | (T : ℝ≥0∞) ≤ EinsteinRelation.Regeneration.firstHittingAbove z.2.1 i level} ≤
        ENNReal.ofReal (C * Real.exp (-κ * lam ^ 2 * T + lam * level))) :
    Integrable (fun z => Real.exp (a * (lam ^ 2 *
      (EinsteinRelation.Regeneration.firstHittingAbove z.2.1 i (b / lam)).toReal))) μ ∧
    (∫ z, Real.exp (a * (lam ^ 2 *
      (EinsteinRelation.Regeneration.firstHittingAbove z.2.1 i (b / lam)).toReal)) ∂μ) ≤
      max 1 (C * Real.exp b) * Real.exp a / (1 - Real.exp (a - κ / 2)) := by
  let τ := fun z : EinsteinRelation.FieldPair d × EinsteinRelation.Regeneration.CoupledSample d =>
    EinsteinRelation.Regeneration.firstHittingAbove z.2.1 i (b / lam)
  have hτ : Measurable τ :=
    ((EinsteinRelation.Regeneration.measurable_firstHittingAbove i).comp
      (measurable_const.prodMk measurable_snd.fst))
  apply scaled_time_exponential_moment_of_tail μ τ hτ (lam ^ 2) κ C b a (by positivity) hC ha haκ
  intro t ht
  have h := hhit t.toNNReal (b / lam) (div_nonneg hb hlam.le)
  rw [ENNReal.ofReal_eq_coe_nnreal ht]
  have heq : -κ * lam ^ 2 * (t.toNNReal : ℝ) + lam * (b / lam) =
      -κ * lam ^ 2 * t + b := by
    rw [Real.coe_toNNReal _ ht]
    field_simp
  have hnn : t.toNNReal = ⟨t, ht⟩ := by
    ext
    exact Real.coe_toNNReal _ ht
  rw [heq, hnn] at h
  exact h

end EinsteinFull.Regeneration
