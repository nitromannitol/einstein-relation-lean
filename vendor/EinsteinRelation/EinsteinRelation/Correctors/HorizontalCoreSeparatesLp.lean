import EinsteinRelation.Correctors.HorizontalCoreLpApproximation
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Continuous

/-! # Horizontal core tests separate scalar `L²(Q)` classes

Source anchors: `paper/main.tex:240–248` (the strong `L²(Q)` setting, and the convention at
line 245 that identities involving the horizontal derivative are tested against horizontally
smooth functions) and `paper/main.tex:688–701` (the corrector gradient, characterized at lines
695–696 by its vanishing pairing against test functions).

The proof takes genuine `L²` core representatives `F n` of a class `f` from
`exists_horizontalCore_Lp_approximation`. Each `F n` is a horizontal test, so the value-test
hypothesis gives `⟪f, F n⟫ = 0` for every `n`. Continuity of the `L²(Q)` inner product carries
this vanishing to the limit `⟪f, f⟫ = 0`, hence `f = 0`.

This is value-test determination only. It does not assume that `f` lies in the core, uses no
`H¹` graph-density premise, and assumes no regularity of observables.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- Pairing an `L²(Q)` class with the `L²` class of a scalar function is the real integral of
the product, through the a.e. representative. Private transport, as in
`HorizontalMollifierRepresentative`. -/
private theorem inner_toLp_eq_integral_mul {d : ℕ} {Q : Measure (FieldPair d)} (g : Lp ℝ 2 Q)
    {G : FieldPair d → ℝ} (hG : MemLp G 2 Q) :
    inner ℝ g (hG.toLp G) = ∫ ω, g ω * G ω ∂Q := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hG.coeFn_toLp] with ω hω
  rw [hω, RCLike.inner_apply, conj_trivial, mul_comm]

/-- A class `f` of the scalar `L²(Q)` space of a stationary probability measure on coefficient
pairs is zero as soon as every horizontal core test `H` has `∫ f · H dQ = 0`. Source
`paper/main.tex:240–248` and `paper/main.tex:688–701`. Value-test determination through the
genuine core `L²` approximation; no `H¹` graph density is assumed. -/
theorem eq_zero_of_horizontalCore_pairing_eq_zero {d : ℕ}
    (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q] (hQ : IsStationary Q)
    (f : Lp ℝ 2 Q)
    (hf : ∀ H : FieldPair d → ℝ, IsHorizontalTest H → (∫ ω, f ω*H ω ∂Q) = 0) : f = 0 := by
  obtain ⟨F, hHor, hF, hlim⟩ := exists_horizontalCore_Lp_approximation Q hQ f
  -- Each core representative is `L²(Q)`-orthogonal to `f`, read through its a.e. representative.
  have hzero : ∀ n, inner ℝ f ((hF n).toLp (F n)) = 0 := fun n => by
    rw [inner_toLp_eq_integral_mul]
    exact hf (F n) (hHor n)
  have hlim_zero : Filter.Tendsto (fun n => inner ℝ f ((hF n).toLp (F n))) Filter.atTop
      (nhds 0) := by
    simp only [hzero]
    exact tendsto_const_nhds
  -- Continuity of the inner product carries the vanishing to the limit `f`.
  have hlim' : Filter.Tendsto (fun n => inner ℝ f ((hF n).toLp (F n))) Filter.atTop
      (nhds (inner ℝ f f)) := tendsto_const_nhds.inner hlim
  have hinner : inner ℝ f f = 0 := tendsto_nhds_unique hlim' hlim_zero
  exact inner_self_eq_zero.1 hinner

end EinsteinRelation.Correctors
