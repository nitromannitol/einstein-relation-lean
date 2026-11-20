import EinsteinFull.Regeneration.BiasedWalkTail
import EinsteinRelation.Regeneration.Construction

/-!
# Forward hitting from a comparison walk

A path that dominates the biased comparison walk at uniformly bounded trial
intervals satisfies the forward-hitting estimate of GMP Lemma 4.2.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation EinsteinRelation.Regeneration Finset
open scoped NNReal ENNReal ProbabilityTheory

namespace EinsteinFull.Regeneration

/-- A bounded-time coupling to the biased walk gives a forward-hitting tail.
The path and comparison walk live on the same probability space. -/
theorem forward_hitting_le_of_biased_walk {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (γ : Ω → Path d) (i : Fin d)
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, X n ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ n, (∫ ω, X n ω ∂μ) = (1 / 5 : ℝ))
    (τ : ℕ → Ω → ℝ≥0) (L g : ℝ) (hL : 0 < L) (hg : 0 < g)
    (htime : ∀ n, ∀ᵐ ω ∂μ, (τ n ω : ℝ) ≤ n * g)
    (hcompare : ∀ n, ∀ᵐ ω ∂μ,
      L * (∑ j ∈ range n, X j ω) ≤ γ ω (τ n ω) i - γ ω 0 i)
    (T : ℝ≥0) (a : ℝ) (ha : 0 ≤ a) :
    μ.real {ω | (T : ℝ≥0∞) ≤ firstHittingAbove (γ ω) i a} ≤
      Real.exp ((a / L) / 5 + 1 / 50 - (T : ℝ) / (100 * g)) := by
  by_cases hT : T = 0
  · subst T
    have he : 0 ≤ (a / L) / 5 + 1 / 50 := by positivity
    have h := (measureReal_le_one : μ.real {ω | ((0 : ℝ≥0) : ℝ≥0∞) ≤
      firstHittingAbove (γ ω) i a} ≤ 1).trans (Real.one_le_exp he)
    simpa only [NNReal.coe_zero, zero_div, sub_zero] using h
  · have hTpos : 0 < (T : ℝ) := by exact_mod_cast (pos_iff_ne_zero.mpr hT)
    let n : ℕ := ⌊(T : ℝ) / (2 * g)⌋₊
    have hdiv : 0 ≤ (T : ℝ) / (2 * g) := by positivity
    have hfloor : (n : ℝ) ≤ (T : ℝ) / (2 * g) := Nat.floor_le hdiv
    have hstep : (n : ℝ) * g < (T : ℝ) := by
      have h := (le_div_iff₀ (by positivity : 0 < 2 * g)).mp hfloor
      nlinarith
    have hsub : ∀ᵐ ω ∂μ, ω ∈ {ω | (T : ℝ≥0∞) ≤ firstHittingAbove (γ ω) i a} →
        ω ∈ {ω | ∑ j ∈ range n, X j ω ≤ a / L} := by
      filter_upwards [htime n, hcompare n] with ω ht hc hh
      have hτ : τ n ω < T := by
        apply NNReal.coe_lt_coe.mp
        exact lt_of_le_of_lt ht hstep
      have hcross : γ ω (τ n ω) i - γ ω 0 i < a := by
        by_contra hnot
        have hhit := firstHittingAbove_le_of_crossing (γ ω) i a (τ n ω) (le_of_not_gt hnot)
        have hlt : ((τ n ω : ℝ≥0) : ℝ≥0∞) < (T : ℝ≥0∞) := ENNReal.coe_lt_coe.mpr hτ
        exact (not_lt_of_ge (hh.trans hhit)) hlt
      apply (le_div_iff₀ hL).2
      nlinarith
    have hmeasure : μ.real {ω | (T : ℝ≥0∞) ≤ firstHittingAbove (γ ω) i a} ≤
        μ.real {ω | ∑ j ∈ range n, X j ω ≤ a / L} := by
      exact ENNReal.toReal_mono (measure_ne_top μ _) (measure_mono_ae hsub)
    have hn : (T : ℝ) / (2 * g) < (n : ℝ) + 1 := Nat.lt_floor_add_one _
    have hexp : (a / L) / 5 - (n : ℝ) / 50 ≤
        (a / L) / 5 + 1 / 50 - (T : ℝ) / (100 * g) := by
      have he : (T : ℝ) / (2 * g) / 50 = (T : ℝ) / (100 * g) := by ring
      linarith
    exact hmeasure.trans ((biased_walk_lower_tail μ X hX hind hbound hmean n (a / L)).trans
      (Real.exp_le_exp.mpr hexp))

/-- A comparison walk with the source's diffusive scales gives the GMP form
of the forward-hitting estimate. -/
theorem scaled_forward_hitting_le_of_biased_walk {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {d : ℕ} (γ : Ω → Path d) (i : Fin d)
    (X : ℕ → Ω → ℝ) (hX : ∀ n, Measurable (X n)) (hind : iIndepFun X μ)
    (hbound : ∀ n, ∀ᵐ ω ∂μ, X n ω ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∀ n, (∫ ω, X n ω ∂μ) = (1 / 5 : ℝ))
    (τ : ℕ → Ω → ℝ≥0) (lam L g : ℝ) (hlam : 0 < lam) (hL : (1 / 5 : ℝ) ≤ L)
    (hg : 0 < g)
    (htime : ∀ n, ∀ᵐ ω ∂μ, (τ n ω : ℝ) ≤ n * (g / lam ^ 2))
    (hcompare : ∀ n, ∀ᵐ ω ∂μ,
      (L / lam) * (∑ j ∈ range n, X j ω) ≤ γ ω (τ n ω) i - γ ω 0 i)
    (T : ℝ≥0) (a : ℝ) (ha : 0 ≤ a) :
    μ {ω | (T : ℝ≥0∞) ≤ firstHittingAbove (γ ω) i a} ≤
      ENNReal.ofReal (Real.exp (1 / 50) *
        Real.exp (-(1 / (100 * g)) * lam ^ 2 * (T : ℝ) + lam * a)) := by
  have hLpos : 0 < L := by linarith
  have hraw := forward_hitting_le_of_biased_walk μ γ i X hX hind hbound hmean τ
    (L / lam) (g / lam ^ 2) (div_pos hLpos hlam) (div_pos hg (sq_pos_of_pos hlam))
    htime hcompare T a ha
  have hspace : (a / (L / lam)) / 5 = (lam * a) / (5 * L) := by field_simp
  have hspace_le : (lam * a) / (5 * L) ≤ lam * a := by
    apply (div_le_iff₀ (by positivity : 0 < 5 * L)).2
    nlinarith [mul_nonneg hlam.le ha]
  have htime_eq : (T : ℝ) / (100 * (g / lam ^ 2)) =
      (1 / (100 * g)) * lam ^ 2 * (T : ℝ) := by field_simp
  have harg : (a / (L / lam)) / 5 + 1 / 50 - (T : ℝ) / (100 * (g / lam ^ 2)) ≤
      1 / 50 + (-(1 / (100 * g)) * lam ^ 2 * (T : ℝ) + lam * a) := by
    rw [hspace, htime_eq]
    linarith
  rw [← ENNReal.ofReal_toReal (measure_ne_top μ _)]
  apply ENNReal.ofReal_le_ofReal
  calc
    _ ≤ _ := hraw
    _ ≤ Real.exp (1 / 50 + (-(1 / (100 * g)) * lam ^ 2 * (T : ℝ) + lam * a)) :=
      Real.exp_le_exp.mpr harg
    _ = _ := Real.exp_add _ _

end EinsteinFull.Regeneration
