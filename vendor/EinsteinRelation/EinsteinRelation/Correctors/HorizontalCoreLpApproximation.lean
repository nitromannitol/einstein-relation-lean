import EinsteinRelation.Correctors.HorizontalCoreLpDensity

/-! # Horizontal core `L²` value approximation

Source anchors: `paper/main.tex:240–248` (the strong `L²(Q)` setting on which the horizontal
derivative acts, and the horizontally smooth core) and `paper/main.tex:545–566` (Step 2, where
classes are smoothed by `S_δ f = ∫ κ_δ(x) f ∘ T_x dx`).

The proof extracts core representatives from the closure statement
`closure_horizontalCore_Lp_eq_univ`: for each `n` the class `f` lies within `1 / (n + 1)` of a core
class, and these representatives converge to `f` in `L²(Q)`. This is an `L²` value approximation
only. No regularity of observables, no `H¹` gradient approximation, and no environmental
continuity is assumed.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Every class of the scalar `L²(Q)` space of a stationary probability measure on coefficient
pairs is the `L²` limit of a sequence of horizontal core representatives. Source
`paper/main.tex:240–248` and `paper/main.tex:545–566`. Value approximation only. -/
theorem exists_horizontalCore_Lp_approximation {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (hQ : IsStationary Q) (f : Lp ℝ 2 Q) :
    ∃ F : ℕ → FieldPair d → ℝ, (∀ n, IsHorizontalTest (F n)) ∧
    ∃ hF : ∀ n, MemLp (F n) 2 Q,
    Filter.Tendsto (fun n => (hF n).toLp (F n)) Filter.atTop (nhds f) := by
  -- The core classes are dense, so `f` lies in their closure.
  have hf : f ∈ (Set.univ : Set (Lp ℝ 2 Q)) := Set.mem_univ f
  rw [← closure_horizontalCore_Lp_eq_univ Q hQ] at hf
  -- Metric form of the closure: each radius `1 / (n + 1)` has a core class inside it.
  have hmem : ∀ n : ℕ, ∃ G : FieldPair d → ℝ, IsHorizontalTest G ∧
      ∃ hG : MemLp G 2 Q, dist (hG.toLp G) f < 1 / ((n : ℝ) + 1) := by
    intro n
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    obtain ⟨b, ⟨G, hG, hGm, rfl⟩, hdist⟩ := Metric.mem_closure_iff.1 hf (1 / ((n : ℝ) + 1)) hpos
    exact ⟨G, hG, hGm, by rw [dist_comm]; exact hdist⟩
  choose F hHor hF hdist using hmem
  refine ⟨F, hHor, hF, ?_⟩
  refine Metric.tendsto_atTop.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hε
  refine ⟨N, fun n hn => ?_⟩
  have hNn : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hle : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
    one_div_le_one_div_of_le (by positivity) (by linarith)
  exact lt_of_lt_of_le (hdist n) (hle.trans hN.le)

end EinsteinRelation.Correctors
