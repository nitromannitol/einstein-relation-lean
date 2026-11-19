import EinsteinFull.Calculus.C16SourceExponentialMaxAssembly
import EinsteinFull.Regeneration.NoReturnFromHitting
import EinsteinRelation.Regeneration.Measurability

/-!
# Moments from regeneration-time tails

An exponential time tail implies finite regeneration time and an integrable duration.
-/

open MeasureTheory Filter
open scoped NNReal ENNReal Topology

namespace EinsteinFull.Regeneration

/-- A nonnegative extended random time with an exponential tail is finite almost surely
and its real embedding has exponential moments below half the tail rate. -/
theorem time_moments_of_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : Ω → ℝ≥0∞) (hτ : Measurable τ)
    (C κ : ℝ) (hC : 0 ≤ C) (hκ : 0 < κ)
    (htail : ∀ t : ℝ, 0 ≤ t → μ {ω | ENNReal.ofReal t < τ ω} ≤
      ENNReal.ofReal (C * Real.exp (-κ * t))) :
    (∀ᵐ ω ∂μ, τ ω ≠ ⊤) ∧
      ∀ a : ℝ, 0 < a → a < κ / 2 →
        Integrable (fun ω => Real.exp (a * (τ ω).toReal)) μ := by
  have harg : Tendsto (fun n : ℕ => -κ * (n : ℝ)) atTop atBot :=
    (tendsto_natCast_atTop_atTop : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop)
      |>.const_mul_atTop_of_neg (neg_lt_zero.mpr hκ)
  have hlim : Tendsto (fun n : ℕ => ENNReal.ofReal
      (C * Real.exp (-κ * (n : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero, ENNReal.ofReal_zero, Function.comp_apply] using
      ENNReal.tendsto_ofReal ((Real.tendsto_exp_atBot.comp harg).const_mul C)
  have hzero : μ {ω | τ ω = ⊤} = 0 := by
    apply le_antisymm _ zero_le
    apply ge_of_tendsto' hlim
    intro n
    calc
      μ {ω | τ ω = ⊤} ≤ μ {ω | ENNReal.ofReal (n : ℝ) < τ ω} := by
        apply measure_mono
        intro ω hω
        change τ ω = ⊤ at hω
        change ENNReal.ofReal (n : ℝ) < τ ω
        rw [hω]
        exact ENNReal.ofReal_lt_top
      _ ≤ _ := htail n n.cast_nonneg
  have hf : ∀ᵐ ω ∂μ, τ ω ≠ ⊤ := by
    rw [ae_iff]
    simpa only [not_not] using hzero
  refine ⟨hf, ?_⟩
  intro a ha hak
  apply EinsteinFull.c16_max_integrable_of_tail hτ.ennreal_toReal
    (fun ω => ENNReal.toReal_nonneg) (le_max_of_le_left hC) ha hak
  intro s hs
  by_cases hs0 : s = 0
  · subst s
    simpa only [mul_zero, neg_zero, Real.exp_zero, mul_one] using
      (measureReal_le_one : μ.real {ω | (0 : ℝ) ≤ (τ ω).toReal} ≤ 1).trans (le_max_right C 1)
  · have hspos : 0 < s := lt_of_le_of_ne hs (Ne.symm hs0)
    have hsub : {ω | s ≤ (τ ω).toReal} ⊆ {ω | ENNReal.ofReal (s / 2) < τ ω} := by
      intro ω hω
      change s ≤ (τ ω).toReal at hω
      have hfin : τ ω ≠ ⊤ := by
        intro htop
        rw [htop, ENNReal.toReal_top] at hω
        linarith
      change ENNReal.ofReal (s / 2) < τ ω
      exact (ENNReal.ofReal_lt_iff_lt_toReal (by positivity) hfin).2 (by linarith)
    have hbound := htail (s / 2) (by positivity)
    have hm : μ.real {ω | s ≤ (τ ω).toReal} ≤ C * Real.exp (-κ * (s / 2)) := by
      have hle := (measure_mono hsub).trans hbound
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      simpa only [measureReal_def, ENNReal.toReal_ofReal (mul_nonneg hC (Real.exp_pos _).le)] using hh
    calc
      _ ≤ C * Real.exp (-κ * (s / 2)) := hm
      _ ≤ max C 1 * Real.exp (-((κ / 2) * s)) := by
        have heq : -κ * (s / 2) = -((κ / 2) * s) := by ring
        rw [heq]
        exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le

/-- An exponential tail gives an integrable real duration. -/
theorem time_integrable_of_exponential_tail {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : Ω → ℝ≥0∞) (hτ : Measurable τ)
    (C κ : ℝ) (hC : 0 ≤ C) (hκ : 0 < κ)
    (htail : ∀ t : ℝ, 0 ≤ t → μ {ω | ENNReal.ofReal t < τ ω} ≤
      ENNReal.ofReal (C * Real.exp (-κ * t))) :
    Integrable (fun ω => (τ ω).toReal) μ := by
  have ha : 0 < κ / 4 := by positivity
  have hi := (time_moments_of_exponential_tail μ τ hτ C κ hC hκ htail).2
    (κ / 4) ha (by linarith)
  apply (hi.div_const (κ / 4)).mono' hτ.ennreal_toReal.aestronglyMeasurable
  filter_upwards [] with ω
  rw [Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg]
  apply (le_div_iff₀ ha).2
  have h := Real.add_one_le_exp ((κ / 4) * (τ ω).toReal)
  linarith

/-- The actual first-regeneration tail supplies finiteness and integrability of its duration. -/
theorem first_regeneration_finite_and_integrable_of_tail {d : ℕ}
    (Q : Measure (EinsteinRelation.FieldPair d)) [IsProbabilityMeasure Q]
    (K : EinsteinRelation.Regeneration.CoupledQuenchedLaws d)
    (hK : EinsteinRelation.Regeneration.HasProbabilityLaws Q K)
    (Δ : ℝ≥0) (lam R : ℝ) (i : Fin d) (C κ : ℝ) (hC : 0 ≤ C) (hκ : 0 < κ)
    (htail : ∀ t : ℝ, 0 ≤ t →
      EinsteinRelation.Regeneration.annealedCoupledLaw Q K
        {q | ENNReal.ofReal t < EinsteinRelation.Regeneration.firstRegenerationTime Δ lam R q.2 i} ≤
          ENNReal.ofReal (C * Real.exp (-κ * t))) :
    (∀ᵐ q ∂EinsteinRelation.Regeneration.annealedCoupledLaw Q K,
      EinsteinRelation.Regeneration.firstRegenerationTime Δ lam R q.2 i ≠ ⊤) ∧
    Integrable (fun q => (EinsteinRelation.Regeneration.firstRegenerationTime Δ lam R q.2 i).toReal)
      (EinsteinRelation.Regeneration.annealedCoupledLaw Q K) := by
  let μ := EinsteinRelation.Regeneration.annealedCoupledLaw Q K
  let : IsProbabilityMeasure μ :=
    EinsteinRelation.Regeneration.annealedCoupledLaw_isProbabilityMeasure Q K hK
  let τ := fun q : EinsteinRelation.FieldPair d × EinsteinRelation.Regeneration.CoupledSample d =>
    EinsteinRelation.Regeneration.firstRegenerationTime Δ lam R q.2 i
  have hm : Measurable τ :=
    (EinsteinRelation.Regeneration.measurable_firstRegenerationTime Δ lam R i).comp measurable_snd
  exact ⟨(time_moments_of_exponential_tail μ τ hm C κ hC hκ htail).1,
    time_integrable_of_exponential_tail μ τ hm C κ hC hκ htail⟩

end EinsteinFull.Regeneration
