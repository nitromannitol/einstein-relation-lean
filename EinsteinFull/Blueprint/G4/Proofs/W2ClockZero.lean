import EinsteinFull.Blueprint.G4.node_clock_u2D_zero_u2D_coefficient
import EinsteinFull.Blueprint.Roots.node_p_u3A_response
import EinsteinFull.Blueprint.Foundation.Proofs.ReducedBounds

open MeasureTheory Filter
open scoped Topology NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation

private theorem clockRate_bounds {d : ℕ} {L r : ℝ}
    {Q : EnvironmentLaw d L r} {Y : QuenchedPathLaws d} {i : Fin d} {lam η : ℝ}
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (hη : HasReducedClockRate Q Y η) (lower upper : ℝ)
    (hb : ∀ᵐ ω ∂reducedLaw Q, ∀ x : Vec d, lower ≤ ω.2 x ∧ ω.2 x ≤ upper) :
    lower ≤ η ∧ η ≤ upper := by
  have hb' : ∀ᵐ ω ∂Q.measure, ∀ x : Vec d,
      lower ≤ clockDensity ω x ∧ clockDensity ω x ≤ upper :=
    ae_of_ae_map Probability.measurable_reduce.aemeasurable hb
  have he : ∀ᵐ ω ∂Q.measure, lower ≤ η ∧ η ≤ upper := by
    filter_upwards [hb', hY, hη] with ω hω hYω hηω
    letI : IsProbabilityMeasure (originLaw Y ω) := hYω.1
    obtain ⟨γ, hγ⟩ := hηω.exists
    have hr : ∀ᶠ t : ℝ≥0 in atTop,
        lower ≤ (Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ) ∧
        (Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ) ≤ upper := by
      filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
      have htR : (0 : ℝ) < (t : ℝ) := NNReal.coe_pos.mpr ht
      have hc := Clock.pathClock_bounds (clockDensity ω) (reduce ω).2.continuous
        lower upper hω γ t
      rw [← Clock.coe_physicalPathClock] at hc
      exact ⟨(le_div_iff₀ htR).2 hc.1, (div_le_iff₀ htR).2 hc.2⟩
    exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hγ (hr.mono fun _ h => h.1),
      le_of_tendsto_of_tendsto hγ tendsto_const_nhds (hr.mono fun _ h => h.2)⟩
  exact he.exists.choose_spec

/-- The clock has zero constant coefficient, and every actual limiting clock
rate inherits the bounds of the actual reduced density. The prescribed graph
premises are retained; this node follows already from definitions and pathwise
clock bounds, independently of response and profile estimates. -/
@[nolint unusedArguments]
theorem node_clock_u2D_zero_u2D_coefficient_of_deps
    (_hresponse : node_p_u3A_responseStmt)
    (_hprofile : node_p_u3A_profileStmt) :
    node_clock_u2D_zero_u2D_coefficientStmt := by
  intro d hd D
  obtain ⟨Λ, A, B, hΛ, _, _, _, hb⟩ :=
    node_eq_u2E_reduced_u2D_bounds_of_deps D.ellipticity D.one_le_ellipticity
  refine ⟨Λ, hΛ, ?_⟩
  intro Q hQ β a μ Z covariance hβ ha hμ hZ hcov P hP
  have hzero (t : ℝ≥0) : clockCorrelation Q (⟨0, by omega⟩ : Fin d) 0
      (P 0) β μ t = 0 := by
    simp only [clockCorrelation, zero_smul, map_zero]
    apply integral_eq_zero_of_ae
    filter_upwards [Lp.coeFn_zero ℂ 2 (reducedLaw Q)] with ω hω
    simp only [hω, Pi.zero_apply, mul_zero]
  refine ⟨hzero, ?_, ?_, ?_, ?_⟩
  · simp [clockGaussianProfile]
  · simp only [hzero, Complex.zero_re, integral_zero]
  · dsimp only
    have hrem (t : ℝ) : kernelProfileRemainder d 0
        ((2 * Real.pi) ^ (-(d : ℝ) / 2) / Real.sqrt (homogenizedCoefficient Q).det / 2 *
          covariance (.inl (⟨0, by omega⟩, ⟨0, by omega⟩)) (.inr ()))
        ((homogenizedCoefficient Q) ⟨0, by omega⟩ ⟨0, by omega⟩ / 2)
        (fun t z => clockCorrelation Q ⟨0, by omega⟩ z (P z) β μ t.toNNReal) t 0 = 0 := by
      simp [kernelProfileRemainder, hzero, complexGaussianProfile]
    simp [hrem, profileTaylorCoefficient, gaussianProfile]
  · intro lam _hlam Y hY η hη
    have hstruct := clockRate_bounds hY hη Λ⁻¹ Λ ((hb d D.dependenceRange Q).2.2.mono
      fun _ h => h.2.1)
    exact ⟨hstruct.1, hstruct.2, clockRate_bounds hY hη⟩

end EinsteinFull.Blueprint
