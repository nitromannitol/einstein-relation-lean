import EinsteinRelation.Clock.ClockExpectation
import EinsteinRelation.Clock.SpatialAverageBound
import EinsteinRelation.Density.LaplaceDensityAbel
import EinsteinRelation.Environment.SourceReducedBoundSupport
import EinsteinRelation.Mobility.ClockEstimateFromSteps

/-! # Discharging the clock premises of the scalar decomposition

`Mobility.ClockEstimateFromSteps` proves `ClockEstimateStep` from three named inputs. This file
proves two of them without further hypotheses:

* `CentredClockAveragingStep` is `Clock.exists_clock_averaging`, the spatial-average bound for the
  centred clock density (`paper/main.tex` 1155-1164);
* `ClockExpectationLimit` follows from the Fubini identity and the fibrewise rate limit of
  `Clock.ClockExpectation`. The clock density is bounded by `sourceReducedBound Λ₀` at every point
  of every regular environment, so the clamp at that level is inactive along almost every path, and
  the clamped fixed-time expectations integrate to the expected clock (`paper/main.tex` 1170-1173).

Only Proposition 6.1, `ScalarDecompositionTwin`, remains an input of the final theorem.
-/

open MeasureTheory Filter
open scoped NNReal

noncomputable section

namespace EinsteinRelation

/-- The centred clock averaging step holds: it is the spatial-average bound
`Clock.exists_clock_averaging`. -/
theorem centredClockAveragingStep_holds : CentredClockAveragingStep :=
  Clock.exists_clock_averaging

/-- For almost every environment, the clock density is bounded by the source constant at every
point. This is the support bound `sourceReducedBound_support`, which holds on every regular
environment. -/
private theorem ae_clockDensity_le_sourceReducedBound {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) :
    ∀ᵐ ω ∂Q.measure, ∀ x : Vec d, clockDensity ω x ≤ sourceReducedBound Λ₀ := by
  filter_upwards [Q.regular] with ω hω x
  exact ((sourceReducedBound_support Q.ellipticity_parameter hω).2.2.1 x).2

/-- Along almost every environment and almost every path from the origin, the clock density is
bounded by the source constant at every time. -/
private theorem ae_path_clockDensity_le {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀)
    (P : QuenchedPathLaws d) :
    ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂(originLaw P ω),
      ∀ s : ℝ≥0, clockDensity ω (pathPosition s γ) ≤ sourceReducedBound Λ₀ :=
  (ae_clockDensity_le_sourceReducedBound Q).mono fun ω hω =>
    Filter.Eventually.of_forall fun γ s => hω (pathPosition s γ)

/-- The clock density bound transfers from the environment-path fibres to the annealed joint law. -/
private theorem ae_joint_clockDensity_le {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (K : ℝ)
    (hbound : ∀ᵐ ω ∂Q, ∀ᵐ γ ∂(originLaw P ω), ∀ s : ℝ≥0, clockDensity ω (pathPosition s γ) ≤ K) :
    ∀ᵐ z ∂(Carriers.annealedCoordinateJoint Q P op),
      ∀ s : ℝ≥0, clockDensity z.1 (pathPosition s z.2) ≤ K :=
  (Clock.ae_annealedCoordinateJoint_mem Q P op
    (Clock.isClosed_clockBoundSet (d := d) K).measurableSet
    (hbound.mono fun ω hω => hω.mono fun γ hγ => hγ)).mono fun _ hz => hz

/-- Where the clock density is bounded by `K`, the clamp at `K` is inactive. Hence the fixed-time
expectation of the clamped clock is the expected clock density at that time. -/
private theorem observationMean_clamp_eq {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (K : ℝ)
    (hK : ∀ᵐ z ∂(Carriers.annealedCoordinateJoint Q P op),
      ∀ s : ℝ≥0, clockDensity z.1 (pathPosition s z.2) ≤ K)
    (u : ℝ) :
    Density.observationMean Q P op (clampedClockAtOrigin K) u =
      ∫ z, (Carriers.reducedObservationAt u.toNNReal z).2 (0 : Vec d)
        ∂(Carriers.annealedCoordinateJoint Q P op) := by
  unfold Density.observationMean
  refine integral_congr_ae ?_
  filter_upwards [hK] with z hz
  refine clampedClockAtOrigin_eq_of_abs_le ?_
  rw [Clock.clockDensity_obs, abs_of_pos (clockDensity_pos z.1 (pathPosition u.toNNReal z.2))]
  exact hz u.toNNReal

/-- For `t ≥ 0`, the expected physical clock at time `t` is the time integral of the expected
clamped clock density. This is the Fubini identity `Clock.integral_physicalPathClock_eq` with the
clamp made inactive by `observationMean_clamp_eq`. -/
private theorem integral_physicalPathClock_eq_primitive {d : ℕ} (Q : Measure (FieldPair d))
    [IsProbabilityMeasure Q] (P : QuenchedPathLaws d)
    (op : ∀ᵐ ω ∂Q, IsProbabilityMeasure (originLaw P ω)) (K : ℝ)
    (hK : ∀ᵐ z ∂(Carriers.annealedCoordinateJoint Q P op),
      ∀ s : ℝ≥0, clockDensity z.1 (pathPosition s z.2) ≤ K)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫ z, (Clock.physicalPathClock z.1 z.2 t.toNNReal : ℝ)
        ∂(Carriers.annealedCoordinateJoint Q P op) =
      ∫ u in (0 : ℝ)..t, Density.observationMean Q P op (clampedClockAtOrigin K) u := by
  have h := Clock.integral_physicalPathClock_eq Q P op K hK t.toNNReal
  rw [Real.coe_toNNReal t ht] at h
  rw [h]
  exact intervalIntegral.integral_congr fun u _ => (observationMean_clamp_eq Q P op K hK u).symm

/-- The clock expectation limit holds. The time averages of the expected clamped clock density
converge to the quenched rate, since they agree with the time averages of the expected physical
clock, which converge by `Clock.tendsto_integral_physicalPathClock_div_of_fiber`. -/
private theorem clockExpectationLimit_holds : ClockExpectationLimit := by
  unfold ClockExpectationLimit
  intro d _hd Λ₀ r₀ Q P' lam _hl0 _hl1 _hGMP op eta hae
  have hbound := ae_path_clockDensity_le Q (P' lam)
  have hlim := Clock.tendsto_integral_physicalPathClock_div_of_fiber Q.measure (P' lam) op
    (sourceReducedBound Λ₀) eta hbound hae
  have hK := ae_joint_clockDensity_le Q.measure (P' lam) op (sourceReducedBound Λ₀) hbound
  refine Filter.Tendsto.congr' ?_ hlim
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact congrArg (fun x : ℝ => x / t)
    (integral_physicalPathClock_eq_primitive Q.measure (P' lam) op (sourceReducedBound Λ₀) hK ht)

/-- **Clock estimate from the scalar decomposition, with its clock premises discharged.** The
internal step `ClockEstimateStep` (`paper/main.tex` 1178, `eq.clock-estimate`) follows from
Proposition 6.1 over the production twins alone. -/
theorem clockEstimateStep_of_scalarDecompositionTwin (H61 : ScalarDecompositionTwin) :
    ClockEstimateStep :=
  clockEstimateStep_of_scalarDecomposition H61 centredClockAveragingStep_holds
    clockExpectationLimit_holds

end EinsteinRelation

end
