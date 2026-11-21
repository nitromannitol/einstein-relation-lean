import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Small-tilt contractions

The product of two passage-moment factors, a failed-trial factor, and a
deterministic bridge factor is strictly contracting at a sufficiently small tilt.
-/

open Filter
open scoped Topology

namespace EinsteinFull.Regeneration

/-- A product of moment bounds with failed-trial mass below one contracts at small tilt. -/
theorem exists_small_tilt_contraction (b A B p : ℝ) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hp : 0 < p) (hp1 : p < 1) :
    ∃ θ : ℝ, 0 < θ ∧ θ ≤ 1 ∧
      0 < Real.exp (b * θ) * (1 + θ * A) ^ 2 * (p + θ * B) ∧
        Real.exp (b * θ) * (1 + θ * A) ^ 2 * (p + θ * B) < 1 := by
  let f : ℝ → ℝ := fun θ => Real.exp (b * θ) * (1 + θ * A) ^ 2 * (p + θ * B)
  have hf : ContinuousAt f 0 := by
    dsimp [f]
    fun_prop
  have hf0 : f 0 < 1 := by simpa [f] using hp1
  have hsmall : ∀ᶠ θ in 𝓝[>] (0 : ℝ), f θ < 1 ∧ θ < 1 ∧ 0 < θ := by
    filter_upwards [(hf.eventually (eventually_lt_nhds hf0)).filter_mono nhdsWithin_le_nhds,
      (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num)).filter_mono nhdsWithin_le_nhds,
      eventually_mem_nhdsWithin] with θ hθ hθ1 hθ0
    exact ⟨hθ, hθ1, hθ0⟩
  obtain ⟨θ, hθ, hθ1, hθ0⟩ := hsmall.exists
  refine ⟨θ, hθ0, hθ1.le, ?_, hθ⟩
  dsimp [f] at *
  positivity

end EinsteinFull.Regeneration
