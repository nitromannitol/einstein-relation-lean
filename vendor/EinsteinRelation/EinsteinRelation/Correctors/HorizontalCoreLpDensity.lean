import EinsteinRelation.Correctors.BoundedMeasurableLpDensity
import EinsteinRelation.Correctors.HorizontalScaledMollifierCore
import EinsteinRelation.Correctors.ScalarMollifierApproximation
import Mathlib.Topology.Closure
import Mathlib.Topology.Neighborhoods
import Mathlib.Topology.NhdsWithin
import Mathlib.Topology.Order.DenselyOrdered

/-! # Horizontal core classes are dense in scalar `L²`

Source anchors: `paper/main.tex:240–248` (the strong `L²(Q)` setting on which the horizontal
derivative acts, and the horizontally smooth core) and `paper/main.tex:545–566` (Step 2, where
classes are smoothed by `S_δ f = ∫ κ_δ(x) f ∘ T_x dx`).

The proof combines three checked inputs:

* `closure_boundedMeasurable_Lp_eq_univ`: the classes with a measurable, everywhere-bounded
  representative are dense in `Lp ℝ 2 Q`;
* `exists_scalarMollifier_Lp_approximation`: for such a representative `F`, the scalar orbit
  smoothings `ε ↦ ∫ κ(x) F(T_{ε • x} ω) dx` lie in `L²(Q)` and converge to the class of `F` as
  `ε → 0`;
* `isHorizontalTest_scaled_mollifier`: for every `ε > 0` the smoothing is a horizontal core, that
  is, measurable, smooth along every orbit, and with bounded coordinate derivatives.

Hence each bounded measurable class is a limit of core classes along `𝓝[>] 0`, so it lies in the
closure of the core classes. Closure minimality then gives the whole space. This is the internal
core density only. No core density, environmental continuity, or `H¹` equivalence is assumed.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The horizontal core classes are dense in the scalar `L²` space of every stationary probability
measure on coefficient pairs: their closure is the whole space. Source `paper/main.tex:240–248`
and `paper/main.tex:545–566`. Internal core density only; no `H¹` equivalence is claimed. -/
theorem closure_horizontalCore_Lp_eq_univ : ∀ {d : ℕ} (Q : Measure (FieldPair d))
  [IsProbabilityMeasure Q], IsStationary Q →
  closure {v : Lp ℝ 2 Q | ∃ F : FieldPair d → ℝ, IsHorizontalTest F ∧
    ∃ hF : MemLp F 2 Q, hF.toLp F = v} = Set.univ := by
  intro d Q _ hQ
  -- Every bounded measurable class is a limit of core classes along `ε ↓ 0`.
  have hsub : {v : Lp ℝ 2 Q | ∃ F : FieldPair d → ℝ, Measurable F ∧
      (∃ M : ℝ, ∀ ω, |F ω| ≤ M) ∧ ∃ hF : MemLp F 2 Q, hF.toLp F = v} ⊆
      closure {v : Lp ℝ 2 Q | ∃ F : FieldPair d → ℝ, IsHorizontalTest F ∧
        ∃ hF : MemLp F 2 Q, hF.toLp F = v} := by
    rintro _ ⟨F, hFm, hFb, hF, rfl⟩
    obtain ⟨hS, hlim⟩ := exists_scalarMollifier_Lp_approximation Q hQ hFm hFb hF
    have hlim' := hlim.mono_left (nhdsWithin_le_nhds (s := Set.Ioi (0 : ℝ)))
    refine mem_closure_of_tendsto hlim' ?_
    refine eventually_nhdsWithin_of_forall fun ε hε => ?_
    exact ⟨_, isHorizontalTest_scaled_mollifier hFm hFb ε (Set.mem_Ioi.mp hε), hS ε, rfl⟩
  -- The bounded measurable classes are dense, and their closure lies in the closure of the cores.
  have hcl := closure_minimal hsub isClosed_closure
  rw [closure_boundedMeasurable_Lp_eq_univ Q] at hcl
  exact Set.eq_univ_of_forall fun v => hcl (Set.mem_univ v)

end EinsteinRelation.Correctors
