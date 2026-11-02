import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Topology.Continuous

/-! # Bounded measurable functions are dense in scalar `L²`

Source anchors: `paper/main.tex:240–248` (the strong `L²(Q)` setting of the translation group and
the horizontal derivative, on which the classes of `Lp ℝ 2 Q` act) and `paper/main.tex:545–566`
(Step 2, where `L²(Q)` classes such as `p_t` are smoothed by `S_δ`). The paper does not state this
density as a separate lemma; it is the bounded-truncation density step used before smoothing.

For a probability measure `Q` on an arbitrary measurable space `Ω`, the classes of `Lp ℝ 2 Q` that
have a measurable, everywhere-bounded representative are dense. The proof uses the pinned density
of `Lp` simple functions. Each `Lp` simple function is the class of a function whose range is
finite, hence measurable and everywhere bounded, and that function agrees almost everywhere with
the `MemLp.toLp` representative. No boundedness, regularity, or density hypothesis on the input is
assumed, and no canonical representative of an `AEStronglyMeasurable` function is used.
-/

open MeasureTheory

namespace EinsteinRelation.Correctors

/-- The class of an `Lp` simple function is the class of a measurable, everywhere-bounded
function. -/
private theorem simpleFunc_mem_boundedMeasurable {Ω : Type*} [MeasurableSpace Ω]
    (Q : Measure Ω) (s : Lp.simpleFunc ℝ 2 Q) :
    (s : Lp ℝ 2 Q) ∈ {v : Lp ℝ 2 Q | ∃ F : Ω → ℝ, Measurable F ∧
      (∃ M : ℝ, ∀ ω, |F ω| ≤ M) ∧ ∃ hF : MemLp F 2 Q, hF.toLp F = v} := by
  have hF : MemLp ⇑(Lp.simpleFunc.toSimpleFunc s) 2 Q := Lp.simpleFunc.memLp s
  have hbound : ∀ ω, |⇑(Lp.simpleFunc.toSimpleFunc s) ω| ≤
      ∑ y ∈ (Lp.simpleFunc.toSimpleFunc s).range, |y| := fun ω =>
    Finset.single_le_sum (fun (y : ℝ) _ => abs_nonneg y)
      (SimpleFunc.mem_range_self (Lp.simpleFunc.toSimpleFunc s) ω)
  have hlp : hF.toLp ⇑(Lp.simpleFunc.toSimpleFunc s) = (s : Lp ℝ 2 Q) := by
    apply Lp.ext
    filter_upwards [hF.coeFn_toLp, Lp.simpleFunc.toSimpleFunc_eq_toFun s] with ω h₁ h₂
    exact h₁.trans h₂
  exact ⟨⇑(Lp.simpleFunc.toSimpleFunc s), (Lp.simpleFunc.toSimpleFunc s).measurable,
    ⟨∑ y ∈ (Lp.simpleFunc.toSimpleFunc s).range, |y|, hbound⟩, hF, hlp⟩

/-- Bounded measurable functions are dense in the scalar `L²` space of every probability measure:
the closure of their classes is the whole space. -/
theorem closure_boundedMeasurable_Lp_eq_univ : ∀ {Ω : Type*} [MeasurableSpace Ω]
  (Q : Measure Ω) [IsProbabilityMeasure Q],
  closure {v : Lp ℝ 2 Q | ∃ F : Ω → ℝ, Measurable F ∧
    (∃ M : ℝ, ∀ ω, |F ω| ≤ M) ∧ ∃ hF : MemLp F 2 Q, hF.toLp F = v} = Set.univ := by
  intro Ω _ Q _
  refine Set.eq_univ_of_forall fun v => ?_
  have hdense : DenseRange ((↑) : Lp.simpleFunc ℝ 2 Q → Lp ℝ 2 Q) :=
    Lp.simpleFunc.denseRange ENNReal.ofNat_ne_top
  have hv : v ∈ closure (Set.range ((↑) : Lp.simpleFunc ℝ 2 Q → Lp ℝ 2 Q)) := by
    rw [hdense.closure_range]
    exact Set.mem_univ v
  refine closure_mono ?_ hv
  rintro _ ⟨s, rfl⟩
  exact simpleFunc_mem_boundedMeasurable Q s

end EinsteinRelation.Correctors
