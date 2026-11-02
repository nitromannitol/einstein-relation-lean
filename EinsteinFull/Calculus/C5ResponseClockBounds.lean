import EinsteinFull.Blueprint.G4.node_p_u3A_response_u23_cesaro_u2D_abel
import EinsteinRelation.Clock.ClockExpectation
open MeasureTheory Filter
open scoped Topology NNReal
namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull
/- SUPERVISOR EXACT CONTRACT (not a declaration/proof):
theorem response_clock_bounds_of_rate
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (Y : QuenchedPathLaws d) (lam : ℝ)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (η : ℝ) (hη : HasReducedClockRate Q Y η) :
    ∀ lower upper : ℝ,
      (∀ᵐ ω ∂reducedLaw Q, ∀ x : Vec d,
        lower ≤ ω.2 x ∧ ω.2 x ≤ upper) →
      (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω, ∀ t : ℝ≥0,
        lower * (t : ℝ) ≤ (Clock.physicalPathClock ω γ t : ℝ) ∧
        (Clock.physicalPathClock ω γ t : ℝ) ≤ upper * (t : ℝ)) ∧
      lower ≤ η ∧ η ≤ upper
-/
/-- Actual density bounds control every path clock and any existing quenched clock rate. -/
theorem response_clock_bounds_of_rate
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (Y : QuenchedPathLaws d) (lam : ℝ)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (η : ℝ) (hη : HasReducedClockRate Q Y η) :
    ∀ lower upper : ℝ,
      (∀ᵐ ω ∂reducedLaw Q, ∀ x : Vec d,
        lower ≤ ω.2 x ∧ ω.2 x ≤ upper) →
      (∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw Y ω, ∀ t : ℝ≥0,
        lower * (t : ℝ) ≤ (Clock.physicalPathClock ω γ t : ℝ) ∧
        (Clock.physicalPathClock ω γ t : ℝ) ≤ upper * (t : ℝ)) ∧
      lower ≤ η ∧ η ≤ upper := by
  intro lower upper hbound
  have hphysical : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      lower ≤ clockDensity ω x ∧ clockDensity ω x ≤ upper :=
    ae_of_ae_map Probability.measurable_reduce.aemeasurable hbound
  have hpath : ∀ᵐ ω ∂Q.measure, ∀ γ : Path d, ∀ t : ℝ≥0,
      lower * (t : ℝ) ≤ (Clock.physicalPathClock ω γ t : ℝ) ∧
      (Clock.physicalPathClock ω γ t : ℝ) ≤ upper * (t : ℝ) := by
    filter_upwards [hphysical] with ω hω
    intro γ t
    exact Clock.pathClock_bounds (clockDensity ω) (reduce ω).2.continuous
      lower upper hω γ t
  constructor
  · filter_upwards [hpath] with ω hω
    exact Filter.Eventually.of_forall hω
  · obtain ⟨ω, hωbound, hωrate, hωMP⟩ :=
      (hpath.and (hη.and hY)).exists
    let : IsProbabilityMeasure (originLaw Y ω) := hωMP.1
    obtain ⟨γ, hγ⟩ := hωrate.exists
    have hratios : ∀ᶠ t : ℝ≥0 in atTop,
        lower ≤ (Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ) ∧
        (Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ) ≤ upper := by
      filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
      have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
      exact ⟨(le_div_iff₀ htR).2 (hωbound γ t).1,
        (div_le_iff₀ htR).2 (hωbound γ t).2⟩
    exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hγ (hratios.mono (fun _ ht => ht.1)),
      le_of_tendsto_of_tendsto hγ tendsto_const_nhds (hratios.mono (fun _ ht => ht.2))⟩

end EinsteinFull.Blueprint
