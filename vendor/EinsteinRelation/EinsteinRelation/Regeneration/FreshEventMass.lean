import EinsteinRelation.Regeneration.AnnealedFreshBit
import EinsteinRelation.Probability.FiniteHistoryMeasurability

/-! # Actual joint fresh event mass

Source `paper/main.tex:353–364`, the fresh-bit mass for a genuine finite-history event in
the first-regeneration decomposition. For an event `A` of the coupled sample that is
measurable for the exact finite-history sigma-algebra `finiteHistorySigma Δ n`, the joint
annealed law satisfies `P(A ∩ {bit n}) = δ · P(A)`. The proof applies the real identity
`integral_annealed_fresh_bit` to the bounded indicator of `A`, rewrites both integrals as
real masses, and converts to ENNReal masses using finiteness of the probability law.
`HasFreshBits` supplies the fibrewise kernel identity; no further premise is assumed, and
the future factorization stays internal.
-/

open MeasureTheory
open scoped NNReal ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
namespace EinsteinRelation.Regeneration

/-- The indicator of a sample event, read through the Bernoulli-path sample, is bounded. -/
private theorem boundedRealTest_indicator_snd {d : ℕ} (A : Set (CoupledSample d)) :
    BoundedRealTest (fun ωz : FieldPair d × CoupledSample d =>
      A.indicator (fun _ : CoupledSample d => (1 : ℝ)) ωz.2) := by
  refine ⟨1, fun ωz => ?_⟩
  by_cases h : ωz.2 ∈ A <;> simp [h]

/-- The sample-event indicator is measurable for the literal product sigma-algebra. -/
private theorem measurable_indicator_snd {d : ℕ} {A : Set (CoupledSample d)}
    (hA : MeasurableSet A) :
    Measurable (fun ωz : FieldPair d × CoupledSample d =>
      A.indicator (fun _ : CoupledSample d => (1 : ℝ)) ωz.2) := by
  have h1 : Measurable (A.indicator (fun _ : CoupledSample d => (1 : ℝ))) :=
    Measurable.indicator measurable_const hA
  exact h1.comp measurable_snd

/-- An event of the exact finite-history sigma-algebra has a finite-history measurable
indicator on the coupled sample. -/
private theorem measurable_indicator_finiteHistory {d : ℕ} (Δ : ℝ≥0) (n : ℕ)
    {A : Set (CoupledSample d)}
    (hA : @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n) A) :
    @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance
      (A.indicator (fun _ : CoupledSample d => (1 : ℝ))) := by
  have h1 : @Measurable (CoupledSample d) ℝ (finiteHistorySigma Δ n) inferInstance
      (fun _ : CoupledSample d => (1 : ℝ)) := measurable_const
  exact Measurable.indicator h1 hA

/-- A real multiplicative mass identity between finite measures gives the ENNReal identity. -/
private theorem measure_eq_ofReal_mul_of_toReal {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [IsFiniteMeasure μ] {S P : Set α} {δ : ℝ} (hδ : 0 ≤ δ)
    (h : (μ S).toReal = δ * (μ P).toReal) :
    μ S = ENNReal.ofReal δ * μ P := by
  calc μ S = ENNReal.ofReal (μ S).toReal :=
        (ENNReal.ofReal_toReal (measure_ne_top μ S)).symm
    _ = ENNReal.ofReal (δ * (μ P).toReal) := by rw [h]
    _ = ENNReal.ofReal δ * ENNReal.ofReal (μ P).toReal := ENNReal.ofReal_mul hδ
    _ = ENNReal.ofReal δ * μ P := by rw [ENNReal.ofReal_toReal (measure_ne_top μ P)]

/-- Source `paper/main.tex:353–364`, the actual joint fresh event mass for a finite-history
event `A`. `HasFreshBits` gives the fibrewise identity for the fresh bit `n` against the
finite past, and integrating it against the actual annealed law gives
`P(A ∩ {bit n}) = δ · P(A)`. The event is arbitrary among finite-history events; no
future factorization is used. -/
theorem measure_annealed_fresh_bit {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (K : CoupledQuenchedLaws d) (_hK : HasProbabilityLaws Q K) (Δ : ℝ≥0) (δ : ℝ)
    (_hδ : 0 ≤ δ) (_hFresh : HasFreshBits Q Δ δ K) (n : ℕ) (A : Set (CoupledSample d))
    (_hA : @MeasurableSet (CoupledSample d) (finiteHistorySigma Δ n) A) :
    annealedCoupledLaw Q K {ωz | ωz.2 ∈ A ∧ ωz.2.2 n = true} =
      ENNReal.ofReal δ * annealedCoupledLaw Q K {ωz | ωz.2 ∈ A} := by
  haveI : IsProbabilityMeasure (annealedCoupledLaw Q K) :=
    annealedCoupledLaw_isProbabilityMeasure Q K _hK
  have hAprod : MeasurableSet A :=
    (EinsteinRelation.Probability.finiteHistorySigma_le (d := d) Δ n) A _hA
  have hbit : Measurable (fun ωz : FieldPair d × CoupledSample d => ωz.2.2 n) :=
    (measurable_pi_apply (X := fun _ : ℕ => Bool) n).comp measurable_snd.snd
  have hbitSet : MeasurableSet {ωz : FieldPair d × CoupledSample d | ωz.2.2 n = true} :=
    hbit (measurableSet_singleton true)
  have hPA : MeasurableSet {ωz : FieldPair d × CoupledSample d | ωz.2 ∈ A} :=
    measurable_snd hAprod
  have hSA : MeasurableSet
      {ωz : FieldPair d × CoupledSample d | ωz.2 ∈ A ∧ ωz.2.2 n = true} :=
    hPA.inter hbitSet
  have hpt_bit : ∀ ωz : FieldPair d × CoupledSample d,
      A.indicator (fun _ : CoupledSample d => (1 : ℝ)) ωz.2 *
          (if ωz.2.2 n = true then (1 : ℝ) else 0) =
        Set.indicator {ωz : FieldPair d × CoupledSample d | ωz.2 ∈ A ∧ ωz.2.2 n = true}
          (fun _ : FieldPair d × CoupledSample d => (1 : ℝ)) ωz := by
    intro ωz
    by_cases hω : ωz.2 ∈ A <;> by_cases hb : ωz.2.2 n = true <;>
      simp [hω, hb]
  have hpt_mem : ∀ ωz : FieldPair d × CoupledSample d,
      A.indicator (fun _ : CoupledSample d => (1 : ℝ)) ωz.2 =
        Set.indicator {ωz : FieldPair d × CoupledSample d | ωz.2 ∈ A}
          (fun _ : FieldPair d × CoupledSample d => (1 : ℝ)) ωz := by
    intro ωz
    by_cases hω : ωz.2 ∈ A <;> simp [hω]
  have hL : (∫ ωz : FieldPair d × CoupledSample d,
        A.indicator (fun _ : CoupledSample d => (1 : ℝ)) ωz.2 *
          (if ωz.2.2 n = true then (1 : ℝ) else 0) ∂annealedCoupledLaw Q K) =
      (annealedCoupledLaw Q K
        {ωz : FieldPair d × CoupledSample d | ωz.2 ∈ A ∧ ωz.2.2 n = true}).toReal := by
    simp only [hpt_bit]
    rw [integral_indicator_const (1 : ℝ) hSA, smul_eq_mul, mul_one, measureReal_def]
  have hR : (∫ ωz : FieldPair d × CoupledSample d,
        A.indicator (fun _ : CoupledSample d => (1 : ℝ)) ωz.2 ∂annealedCoupledLaw Q K) =
      (annealedCoupledLaw Q K {ωz : FieldPair d × CoupledSample d | ωz.2 ∈ A}).toReal := by
    simp only [hpt_mem]
    rw [integral_indicator_const (1 : ℝ) hPA, smul_eq_mul, mul_one, measureReal_def]
  have hH : Measurable (fun ωz : FieldPair d × CoupledSample d =>
      A.indicator (fun _ : CoupledSample d => (1 : ℝ)) ωz.2) :=
    measurable_indicator_snd hAprod
  have hkey : (∫ ωz : FieldPair d × CoupledSample d,
        A.indicator (fun _ : CoupledSample d => (1 : ℝ)) ωz.2 *
          (if ωz.2.2 n = true then (1 : ℝ) else 0) ∂annealedCoupledLaw Q K) =
      δ * ∫ ωz : FieldPair d × CoupledSample d,
        A.indicator (fun _ : CoupledSample d => (1 : ℝ)) ωz.2 ∂annealedCoupledLaw Q K :=
    integral_annealed_fresh_bit Q K _hK Δ δ _hFresh n
      (fun ωz : FieldPair d × CoupledSample d =>
        A.indicator (fun _ : CoupledSample d => (1 : ℝ)) ωz.2)
      hH (boundedRealTest_indicator_snd A)
      (fun ω => measurable_indicator_finiteHistory Δ n _hA)
  rw [hL, hR] at hkey
  exact measure_eq_ofReal_mul_of_toReal _hδ hkey

end EinsteinRelation.Regeneration
