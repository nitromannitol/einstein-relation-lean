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
      _ = (n : ℝ) * P.real (S n) := by simp [hpres, nsmul_eq_mul]
  · exact tendsto_nat_mul_measureReal_sq_tail_zero f hf hf2 hδ

end EinsteinFull.External.DFGW
