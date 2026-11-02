import EinsteinFull.Calculus.S1SharpBoundSupport
import EinsteinRelation.Sharpness.ScalarSmoothBorel

/-! Borel measurability of the set of smooth continuous functions whose iterated coordinate
derivatives are bounded at a countable dense set of points by a prescribed sequence. This is the
measurable carrier used to turn a pointwise derivative bound for every constructed physical pair
into an almost-sure bound under the pushforward law (`paper/main.tex:1534–1541`). -/

open MeasureTheory Filter
open scoped Topology

namespace EinsteinFull.Calculus.S1

open EinsteinRelation EinsteinRelation.Sharpness

variable {d : ℕ}

/-- The smooth continuous functions. -/
def smoothSet (d : ℕ) : Set C(Vec d, ℝ) := {f | ContDiff ℝ (⊤ : ℕ∞) (fun x => f x)}

theorem measurableSet_smoothSet : MeasurableSet (smoothSet d) :=
  measurableSet_contDiff_continuousMap

/-- The iterated coordinate derivative of a continuous function at a point, set to zero off the
smooth set. -/
noncomputable def jetEval (l : List (Fin d)) (x : Vec d) (f : C(Vec d, ℝ)) : ℝ :=
  (smoothSet d).indicator (fun f : C(Vec d, ℝ) =>
    iteratedCoordinateDerivative l (fun y => f y) x) f

theorem measurable_jetEval (l : List (Fin d)) : ∀ x : Vec d, Measurable (jetEval l x) := by
  induction l with
  | nil =>
    intro x
    exact ((continuous_eval_const x).measurable).indicator measurableSet_smoothSet
  | cons j l ih =>
    intro x
    have hg : ∀ n : ℕ, Measurable (fun f : C(Vec d, ℝ) =>
        ((n : ℝ) + 1) * (jetEval l (x + (1 / ((n : ℝ) + 1)) • unitVector j) f - jetEval l x f)) :=
      fun n => (((ih _).sub (ih x)).const_mul _)
    refine measurable_of_tendsto_metrizable hg (tendsto_pi_nhds.2 fun f => ?_)
    by_cases hf : f ∈ smoothSet d
    · have hu : ContDiff ℝ (⊤ : ℕ∞) (iteratedCoordinateDerivative l (fun y => f y)) :=
        contDiff_iteratedCoordinateDerivative _ hf l
      have hev : ∀ y, jetEval l y f = iteratedCoordinateDerivative l (fun y => f y) y :=
        fun y => Set.indicator_of_mem hf _
      have hxd : HasFDerivAt (iteratedCoordinateDerivative l (fun y => f y))
          (fderiv ℝ (iteratedCoordinateDerivative l (fun y => f y)) x) x :=
        (hu.differentiable (by simp) x).hasFDerivAt
      have h1 : HasDerivAt (fun t : ℝ => x + t • unitVector j) (unitVector j) 0 := by
        simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (unitVector j)).const_add x
      have h2 : HasFDerivAt (iteratedCoordinateDerivative l (fun y => f y))
          (fderiv ℝ (iteratedCoordinateDerivative l (fun y => f y)) x)
          (x + (0 : ℝ) • unitVector j) := by simpa using hxd
      have hline := h2.comp_hasDerivAt (0 : ℝ) h1
      have hslope := hline.tendsto_slope_zero
      have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[≠] 0) :=
        tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
          Eventually.of_forall fun n => (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)).ne'⟩
      have hlim := hslope.comp hseq
      have hval : jetEval (j :: l) x f =
          fderiv ℝ (iteratedCoordinateDerivative l (fun y => f y)) x (unitVector j) :=
        Set.indicator_of_mem hf _
      rw [hval]
      refine hlim.congr fun n => ?_
      simp [hev, smul_eq_mul]
    · have h0 : ∀ (l : List (Fin d)) (y : Vec d), jetEval l y f = 0 :=
        fun l y => Set.indicator_of_notMem hf _
      simp only [h0, sub_self, mul_zero]
      exact tendsto_const_nhds

/-- Smooth functions with `|∂^l f x| ≤ C l` at every point `x` of `D`. -/
def coordBoundSet (D : Set (Vec d)) (C : List (Fin d) → ℝ) : Set C(Vec d, ℝ) :=
  {f | f ∈ smoothSet d ∧ ∀ l, ∀ x ∈ D, |iteratedCoordinateDerivative l (fun y => f y) x| ≤ C l}

theorem measurableSet_coordBoundSet {D : Set (Vec d)} (hD : D.Countable)
    (C : List (Fin d) → ℝ) : MeasurableSet (coordBoundSet D C) := by
  have hset : coordBoundSet D C =
      smoothSet d ∩ ⋂ l : List (Fin d), ⋂ x ∈ D, {f | |jetEval l x f| ≤ C l} := by
    ext f
    simp only [coordBoundSet, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_iInter]
    constructor
    · rintro ⟨hf, h⟩
      refine ⟨hf, fun l x hx => ?_⟩
      have : jetEval l x f = iteratedCoordinateDerivative l (fun y => f y) x :=
        Set.indicator_of_mem hf _
      rw [this]
      exact h l x hx
    · rintro ⟨hf, h⟩
      refine ⟨hf, fun l x hx => ?_⟩
      have : jetEval l x f = iteratedCoordinateDerivative l (fun y => f y) x :=
        Set.indicator_of_mem hf _
      rw [← this]
      exact h l x hx
  rw [hset]
  refine measurableSet_smoothSet.inter (MeasurableSet.iInter fun l =>
    MeasurableSet.biInter hD fun x _ => ?_)
  exact measurableSet_le (continuous_abs.measurable.comp (measurable_jetEval l x))
    measurable_const

/-- On a dense set the bounds extend to every point. -/
theorem coordBoundSet_bound {D : Set (Vec d)} (hD : Dense D) {C : List (Fin d) → ℝ}
    {f : C(Vec d, ℝ)} (hf : f ∈ coordBoundSet D C) (l : List (Fin d)) (x : Vec d) :
    |iteratedCoordinateDerivative l (fun y => f y) x| ≤ C l := by
  have hcont : Continuous (iteratedCoordinateDerivative l (fun y => f y)) :=
    (contDiff_iteratedCoordinateDerivative _ hf.1 l).continuous
  have hcl : IsClosed {x | |iteratedCoordinateDerivative l (fun y => f y) x| ≤ C l} :=
    isClosed_le (continuous_abs.comp hcont) continuous_const
  have h := hcl.closure_subset_iff.2 (fun y hy => hf.2 l y hy)
  rw [hD.closure_eq] at h
  exact h (Set.mem_univ x)

end EinsteinFull.Calculus.S1
