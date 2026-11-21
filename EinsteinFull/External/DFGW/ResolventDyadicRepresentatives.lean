import EinsteinFull.External.DFGW.ResolventDifferenceDyadicTail

/-! # Resolvent representatives at dyadic times

The chosen representative of a resolvent difference equals the difference of the chosen
resolvent representatives simultaneously at countably many dyadic trajectory evaluations.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation Filter
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Resolvent differences agree with pointwise differences simultaneously on the long dyadic
grids, almost surely. -/
theorem ae_resolvent_difference_dyadic
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (f : Lp ℝ 2 μ) (m : ℕ) :
    ∀ᵐ η ∂P, ∀ n r k : ℕ,
      let F := transitionResolventDomain hP (reciprocalShift n) f -
        transitionResolventDomain hP (reciprocalShift m) f
      (F : Lp ℝ 2 μ) (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)) =
        transitionResolvent hP (reciprocalShift n) f
          (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)) -
        transitionResolvent hP (reciprocalShift m) f
          (η (dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k)) := by
  apply ae_all_iff.mpr
  intro n
  apply ae_all_iff.mpr
  intro r
  apply ae_all_iff.mpr
  intro k
  let t : ℝ := dyadicGridTime ((n + 1 : ℕ) : ℝ≥0) r k
  have hev : MeasurePreserving (fun η : C(ℝ, S) => η t) P μ :=
    ⟨(continuous_eval_const t).measurable, hP.marginal t⟩
  have h := hev.quasiMeasurePreserving.ae
    (Lp.coeFn_sub (transitionResolvent hP (reciprocalShift n) f)
      (transitionResolvent hP (reciprocalShift m) f))
  filter_upwards [h] with η hη
  exact hη

end EinsteinFull.External.DFGW
