import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Probability.LocalSigma
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.Floor
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Group.Arithmetic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions

open MeasureTheory EinsteinRelation
open scoped NNReal ENNReal BigOperators

/-! # Bernoulli shift at a random time

The time-indexed Bernoulli shift of `paper/main.tex:283–286`, with the environment
and Bernoulli indexing recorded after regeneration in `paper/main.tex:331–340`.
This file records only its joint measurability in the time and the Bernoulli path.
-/

namespace EinsteinRelation.Probability

/-- The shifted Bernoulli sequence `n ↦ β_{⌊t/Δ⌋₊ + n}` is jointly measurable in
the pair `(t, β)` for the product σ-algebra. -/
theorem measurable_time_indexed_bit_shift (Δ : ℝ≥0) :
    Measurable (fun p : ℝ≥0 × (ℕ → Bool) =>
      fun n => p.2 (Nat.floor ((p.1 : ℝ) / (Δ : ℝ)) + n)) := by
  -- The random index `⌊t/Δ⌋₊ : ℕ` is measurable in the pair `(t, β)`.
  have hcoe : Measurable (fun p : ℝ≥0 × (ℕ → Bool) => (p.1 : ℝ)) :=
    measurable_coe_nnreal_real.comp measurable_fst
  have hk : Measurable (fun p : ℝ≥0 × (ℕ → Bool) =>
      Nat.floor ((p.1 : ℝ) / (Δ : ℝ))) :=
    (hcoe.div_const (Δ : ℝ)).nat_floor
  -- Coordinatewise measurability, then evaluation at a countable random index.
  refine measurable_pi_iff.mpr (fun n => ?_)
  have hjoint : Measurable (fun q : ℕ × (ℕ → Bool) => q.2 (q.1 + n)) := by
    refine measurable_from_prod_countable_right (fun k => ?_)
    exact measurable_pi_apply (k + n)
  exact hjoint.comp (hk.prodMk measurable_snd)

end EinsteinRelation.Probability
