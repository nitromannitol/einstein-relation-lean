import EinsteinFull.External.DFGW.FutureCylinderMarkov
import Mathlib.MeasureTheory.Function.ConditionalExpectation.CondexpL2

/-! # State measurability of future cylinder projections

The square-integrable projection of a finite future cylinder on the past is measurable with
respect to the current state.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A bounded future cylinder is square integrable. -/
theorem futureCylinder_memLp (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (xs : List (ℝ≥0 × (S → ℝ))) (hxs : FutureCylinderAdmissible xs) (s : ℝ) :
    MemLp (futureCylinder xs s) 2 P := by
  let : IsProbabilityMeasure P := hP.probability
  obtain ⟨hm, C, hC⟩ := (futureCylinder_measurable_bounded hP xs hxs).2 s
  exact MemLp.of_bound hm.aestronglyMeasurable C
    (ae_of_all P fun η => by simpa only [Real.norm_eq_abs] using hC η)

/-- The past `L²` projection of a future cylinder is current-state measurable. -/
theorem condExpL2_futureCylinder_state_measurable (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (xs : List (ℝ≥0 × (S → ℝ))) (hxs : FutureCylinderAdmissible xs) :
    AEStronglyMeasurable[MeasurableSpace.comap (fun η : C(ℝ, S) => η 0) inferInstance]
      (condExpL2 ℝ ℝ ((Draft.dfgwPast (S := S)).le 0)
        ((futureCylinder_memLp hP xs hxs 0).toLp (futureCylinder xs 0)) : Lp ℝ 2 P) P := by
  let : IsProbabilityMeasure P := hP.probability
  have hrep := (futureCylinder_memLp hP xs hxs 0).condExpL2_ae_eq_condExp
    (𝕜 := ℝ) ((Draft.dfgwPast (S := S)).le 0)
  have hmark := condExp_futureCylinder hP xs hxs 0
  have hm : Measurable[MeasurableSpace.comap (fun η : C(ℝ, S) => η 0) inferInstance]
      (fun η : C(ℝ, S) => futureCylinderKernel T xs (η 0)) :=
    (futureCylinder_measurable_bounded hP xs hxs).1.1.comp (comap_measurable _)
  exact hm.stronglyMeasurable.aestronglyMeasurable.congr (hrep.trans hmark).symm

end EinsteinFull.External.DFGW
