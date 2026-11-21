import EinsteinFull.External.DFGW.Semigroup
import Mathlib.MeasureTheory.Function.L2Space
import MarkovProcess.Semigroup.Generator

/-! # Pairing semigroup orbits with trajectory events

A bounded time integral of an `L²` semigroup orbit commutes with integration over a
trajectory event after evaluating at the initial state.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Integrating an orbit against a trajectory event commutes with the time integral. -/
theorem setIntegral_transition_orbit (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (g : Lp ℝ 2 μ) (t : ℝ≥0) (B : Set C(ℝ, S)) (hB : MeasurableSet B) :
    (∫ η in B, (∫ u in (0 : ℝ)..t, transitionSemigroup hP u.toNNReal g) (η 0) ∂P) =
      ∫ u in (0 : ℝ)..t, ∫ η in B, transitionSemigroup hP u.toNNReal g (η 0) ∂P := by
  let : IsProbabilityMeasure P := hP.probability
  let hev : MeasurePreserving (fun η : C(ℝ, S) => η (0 : ℝ)) P μ :=
    ⟨(continuous_eval_const (0 : ℝ)).measurable, hP.marginal 0⟩
  let E : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 P :=
    (Lp.compMeasurePreservingₗᵢ ℝ _ hev).toContinuousLinearMap
  let I : Lp ℝ 2 P := indicatorConstLp 2 hB (measure_ne_top P B) (1 : ℝ)
  let L : Lp ℝ 2 μ →L[ℝ] ℝ := (innerSL ℝ I).comp E
  have hL (f : Lp ℝ 2 μ) : L f = ∫ η in B, f (η 0) ∂P := by
    change inner ℝ I (Lp.compMeasurePreserving _ hev f) = _
    rw [L2.inner_indicatorConstLp_one hB (measure_ne_top P B)]
    apply setIntegral_congr_ae hB
    filter_upwards [Lp.coeFn_compMeasurePreserving f hev] with η hη _
    simpa only [Function.comp_apply] using hη
  have hint : IntervalIntegrable (fun u : ℝ => transitionSemigroup hP u.toNNReal g)
      volume 0 t := ((transitionSemigroup hP).continuous_operator_toNNReal g).intervalIntegrable _ _
  have h := L.intervalIntegral_comp_comm hint
  simp_rw [hL] at h
  exact h.symm

end EinsteinFull.External.DFGW
