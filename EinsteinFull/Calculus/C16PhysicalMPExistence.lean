import EinsteinFull.Calculus.C16FoundationInstantiation
import EinsteinFull.Calculus.C16InverseClockFamily
import EinsteinFull.Calculus.C16RegularTimeChange

/-! Measurable actual reduced and physical martingale-problem families. -/

namespace EinsteinFull

open EinsteinRelation MeasureTheory ProbabilityTheory

/-- The actual reduced martingale problem has a Markov kernel of solutions
on every regular environment. -/
theorem c16_actual_reduced_mp_kernel {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) (i : Fin d) (lam : ℝ) :
    ∃ PY : QuenchedPathLaws d, IsMarkovKernel PY ∧
      ∀ ω : FieldPair d, IsRegular Λ₀ ω →
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω)) := by
  exact foundation_reduced_actual_kernel hd hΛ i lam

/-- A common reduced family and its measurable inverse-clock transport solve
the reduced and physical martingale problems almost surely. -/
theorem c16_physical_reduced_mp_exists_with_inverse_clock
    (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) :
    ∃ PX PY : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) ∧
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω))) ∧
      ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
        PX (0, ω) = Measure.map
          (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)
          (PY (0, ω)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨PY, _, hPY⟩ := c16_actual_reduced_mp_kernel hd hΛ i lam
  have hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω)) := by
    filter_upwards [Q.regular] with ω hω
    exact hPY ω hω
  obtain ⟨PX, hPX⟩ := c16_inverse_clock_quenched_family_of_reduced_mp
    d Λ₀ r₀ Q i lam PY hY
  refine ⟨PX, PY, ?_, hY, hPX⟩
  filter_upwards [Q.regular, hY, hPX] with ω hω hYω hPXω
  rw [hPXω hω]
  exact c16_time_change_solves_of_regular hΛ hω i lam 0 hYω

end EinsteinFull
