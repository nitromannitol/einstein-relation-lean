import EinsteinFull.External.DFGW.SquareIntegrableTail
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! # Maximal tails of stationary sequences

A square-integrable stationary sequence has no increments of order `√n` among its first `n`
terms with asymptotically positive probability.
-/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.External.DFGW

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]

/-- The maximal squared value in a stationary square-integrable sequence is `o(n)` in
probability. -/
theorem tendsto_measureReal_max_stationary_sq (θ : Ω → Ω) (hθ : MeasurePreserving θ P P)
    (f : Ω → ℝ) (hf : StronglyMeasurable f) (hf2 : MemLp f 2 P)
    {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P.real {ω | ∃ k < n, δ * n ≤ f ((θ^[k]) ω) ^ 2})
      atTop (𝓝 0) := by
  let S : ℕ → Set Ω := fun n => {ω | δ * n ≤ f ω ^ 2}
  have hS (n : ℕ) : MeasurableSet (S n) :=
    measurableSet_le measurable_const (hf.measurable.pow_const 2)
  have hpres (n k : ℕ) : P.real ((θ^[k]) ⁻¹' S n) = P.real (S n) := by
    simp only [Measure.real, (hθ.iterate k).measure_preimage (hS n).nullMeasurableSet]
  apply squeeze_zero (g := fun n : ℕ => (n : ℝ) * P.real (S n))
  · intro n
    exact measureReal_nonneg
  · intro n
    have heq : {ω | ∃ k < n, δ * n ≤ f ((θ^[k]) ω) ^ 2} =
        ⋃ k ∈ Finset.range n, (θ^[k]) ⁻¹' S n := by
      ext ω
      simp [S]
    rw [heq]
    calc
      P.real (⋃ k ∈ Finset.range n, (θ^[k]) ⁻¹' S n) ≤
          ∑ k ∈ Finset.range n, P.real ((θ^[k]) ⁻¹' S n) :=
        measureReal_biUnion_finset_le _ _
      _ = (n : ℝ) * P.real (S n) := by
        simp only [hpres, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · exact tendsto_nat_mul_measureReal_sq_tail_zero f hf hf2 hδ

/-- The same maximal estimate holds for any sequence whose terms agree almost everywhere with
measure-preserving transforms of one square-integrable variable. -/
theorem tendsto_measureReal_max_same_distribution_sq (θ : ℕ → Ω → Ω)
    (hθ : ∀ k, MeasurePreserving (θ k) P P) (f : Ω → ℝ)
    (hf : StronglyMeasurable f) (hf2 : MemLp f 2 P) (g : ℕ → Ω → ℝ)
    (hg : ∀ k, g k =ᵐ[P] fun ω => f (θ k ω)) {δ : ℝ} (hδ : 0 < δ) :
    Tendsto (fun n : ℕ => P.real {ω | ∃ k < n, δ * n ≤ (g k ω) ^ 2})
      atTop (𝓝 0) := by
  let S : ℕ → Set Ω := fun n => {ω | δ * n ≤ f ω ^ 2}
  have hS (n : ℕ) : MeasurableSet (S n) :=
    measurableSet_le measurable_const (hf.measurable.pow_const 2)
  have hpres (n k : ℕ) : P.real {ω | δ * n ≤ (g k ω) ^ 2} = P.real (S n) := by
    have heq : {ω | δ * n ≤ (g k ω) ^ 2} =ᵐ[P] (θ k) ⁻¹' S n := by
      filter_upwards [hg k] with ω hω
      simp only [Set.mem_ofPred_eq, Set.mem_preimage, S, hω]
    simp only [Measure.real, measure_congr heq,
      (hθ k).measure_preimage (hS n).nullMeasurableSet]
  apply squeeze_zero (g := fun n : ℕ => (n : ℝ) * P.real (S n))
  · intro n
    exact measureReal_nonneg
  · intro n
    have heq : {ω | ∃ k < n, δ * n ≤ (g k ω) ^ 2} =
        ⋃ k ∈ Finset.range n, {ω | δ * n ≤ (g k ω) ^ 2} := by
      ext ω
      simp
    rw [heq]
    calc
      P.real (⋃ k ∈ Finset.range n, {ω | δ * n ≤ (g k ω) ^ 2}) ≤
          ∑ k ∈ Finset.range n, P.real {ω | δ * n ≤ (g k ω) ^ 2} :=
        measureReal_biUnion_finset_le (μ := P) (Finset.range n)
          (fun k => {ω | δ * n ≤ (g k ω) ^ 2})
      _ = (n : ℝ) * P.real (S n) := by
        simp only [hpres, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  · exact tendsto_nat_mul_measureReal_sq_tail_zero f hf hf2 hδ

end EinsteinFull.External.DFGW
