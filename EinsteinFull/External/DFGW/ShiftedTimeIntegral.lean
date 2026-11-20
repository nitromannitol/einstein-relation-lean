import EinsteinFull.External.DFGW.ConditionalTimeIntegral
import EinsteinFull.External.DFGW.ShiftedMarkov

/-! # Conditional time integrals at shifted times

Stationarity transports the conditional time-integral identity from the origin to any
nonnegative time.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Conditional expectation of a future time integral at a shifted time. -/
theorem condExp_shifted_time_integral (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (g : Lp ℝ 2 μ) (s t : ℝ≥0) :
    P[fun η : C(ℝ, S) => ∫ u in (0 : ℝ)..t, g (η (u + s)) |
      Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] =ᵐ[P]
      fun η => (∫ u in (0 : ℝ)..t, transitionSemigroup hP u.toNNReal g) (η s) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  have hσ : Draft.dfgwCoordSigma (S := S) (Set.Iic 0) ≤
      Draft.dfgwTrajectoryMeasurableSpace (S := S) := (Draft.dfgwPast (S := S)).le 0
  have hi : Integrable (fun η : C(ℝ, S) => ∫ u in (0 : ℝ)..t, g (η u)) P :=
    (integral_time_observable hP g ((Lp.memLp g).integrable one_le_two) t.coe_nonneg).1
  have hi' : Integrable (fun η : C(ℝ, S) => ∫ u in (0 : ℝ)..t, g (η u))
      (P.map (Draft.dfgwShift s)) := by
    rw [hP.stationary]
    exact hi
  have hc := EinsteinFull.condExp_map_comp (measurable_shift (S := S) s) hσ hi'
  rw [hP.stationary, comap_shift_past s] at hc
  have hm := condExp_time_integral hP g t
  have hp : MeasurePreserving (Draft.dfgwShift (S := S) s) P P :=
    ⟨measurable_shift s, hP.stationary s⟩
  have hm' := hp.quasiMeasurePreserving.ae hm
  filter_upwards [hc, hm'] with η hcη hmη
  simpa only [Function.comp_def, Draft.dfgwShift, ContinuousMap.coe_comp,
    ContinuousMap.coe_mk, zero_add] using hcη.symm.trans hmη

end EinsteinFull.External.DFGW
