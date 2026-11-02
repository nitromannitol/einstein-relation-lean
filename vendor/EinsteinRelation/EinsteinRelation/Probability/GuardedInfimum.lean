import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # Guarded countable infima

The first eligible time in the regeneration recursion is an infimum over the countable
index `n : ℕ` of the times `f n ω`, restricted to the sample-dependent eligible set
`{n | p n ω}`, `paper/main.tex:294–322`. Measurability reduces to countable infima and a
measurable selection between `f n ω` and `⊤`.
-/

open MeasureTheory
open scoped ENNReal

namespace EinsteinRelation.Probability

/-- The infimum of `f n ω` over the sample-dependent eligible indices `{n | p n ω}` is
measurable whenever each `f n` and each eligibility set is measurable. An empty eligible set
gives `⊤`, the convention for an empty infimum in `ℝ≥0∞`. -/
theorem measurable_guarded_nat_iInf {Ω : Type*} [MeasurableSpace Ω]
    (f : ℕ → Ω → ℝ≥0∞) (p : ℕ → Ω → Prop)
    (hf : ∀ n, Measurable (f n)) (hp : ∀ n, MeasurableSet {ω | p n ω}) :
    Measurable (fun ω => ⨅ (n : ℕ) (_ : p n ω), f n ω) := by
  classical
  have hg : ∀ n, Measurable (fun ω => if p n ω then f n ω else ⊤) := fun n =>
    Measurable.ite (hp n) (hf n) measurable_const
  have key : ∀ ω, (⨅ (n : ℕ) (_ : p n ω), f n ω) = ⨅ n, (if p n ω then f n ω else ⊤) :=
    fun ω => iInf_congr fun n => iInf_eq_if (f n ω)
  simp only [key]
  exact Measurable.iInf hg

end EinsteinRelation.Probability
