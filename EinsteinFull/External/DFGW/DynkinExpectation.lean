import EinsteinFull.External.DFGW.MarkovGenerator
import EinsteinFull.External.DFGW.ShiftedTimeIntegral

/-! # The conditional Dynkin identity

For a generator-domain observable, its future value minus the integrated generator has
conditional mean equal to its present value.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- The conditional Dynkin identity for a square-integrable generator-domain observable. -/
theorem condExp_dynkin_shift (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (s t : ℝ≥0) (f : (transitionSemigroup hP).generatorDomain) :
    P[fun η : C(ℝ, S) => (f : Lp ℝ 2 μ) (η ((t : ℝ) + s)) -
      ∫ u in (0 : ℝ)..t, (transitionSemigroup hP).generator f (η (u + s)) |
      Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] =ᵐ[P]
      fun η => (f : Lp ℝ 2 μ) (η s) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let g := (transitionSemigroup hP).generator f
  let A : C(ℝ, S) → ℝ := fun η => (f : Lp ℝ 2 μ) (η ((t : ℝ) + s))
  let B : C(ℝ, S) → ℝ := fun η => ∫ u in (0 : ℝ)..t, g (η (u + s))
  have hev : MeasurePreserving (fun η : C(ℝ, S) => η ((t : ℝ) + s)) P μ :=
    ⟨(continuous_eval_const _).measurable, hP.marginal _⟩
  have hA : Integrable A P := ((Lp.memLp (f : Lp ℝ 2 μ)).comp_measurePreserving hev).integrable one_le_two
  have hB0 : Integrable (fun η : C(ℝ, S) => ∫ u in (0 : ℝ)..t, g (η u)) P :=
    (integral_time_observable hP g ((Lp.memLp g).integrable one_le_two) t.coe_nonneg).1
  have hshift : MeasurePreserving (Draft.dfgwShift (S := S) s) P P :=
    ⟨measurable_shift s, hP.stationary s⟩
  have hB : Integrable B P := by
    have h := hshift.integrable_comp_of_integrable hB0
    simpa only [B, Function.comp_def, Draft.dfgwShift, ContinuousMap.coe_comp,
      ContinuousMap.coe_mk] using h
  have hgen := condExp_shifted_generator hP s t f
  have htime := condExp_shifted_time_integral hP g s t
  have hsub := condExp_sub hA hB (Draft.dfgwCoordSigma (Set.Iic (s : ℝ)))
  filter_upwards [hgen, htime, hsub] with η hgη htη hsη
  change P[A - B | Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] η = _ at hsη
  change P[A | Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] η = _ at hgη
  change P[B | Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] η = _ at htη
  change P[A - B | Draft.dfgwCoordSigma (Set.Iic (s : ℝ))] η = _
  rw [hsη, Pi.sub_apply, hgη, htη]
  exact add_sub_cancel_right _ _

end EinsteinFull.External.DFGW
