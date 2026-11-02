import EinsteinFull.Calculus.S4PathwiseV2Support

/-!
# Joint inverse-clock transport of quenched kernels

The joint path map is already available as `timeChangeFamily`. Kernel products
require s-finiteness; restricting to probability fibers provides the construction
for a kernel solving the reduced martingale problem almost everywhere.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull
open EinsteinRelation

/-- The measurable inverse-clock family construction for an s-finite input kernel. -/
theorem c16_inverse_clock_quenched_family_of_isSFiniteKernel
    (d : ℕ) (_hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (PY : QuenchedPathLaws d) [IsSFiniteKernel PY] :
    ∃ PX : QuenchedPathLaws d, ∀ᵐ ω ∂Q.measure,
      ∀ hω : IsRegular Λ₀ ω,
        PX (0, ω) = Measure.map
          (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)
          (PY (0, ω)) := by
  refine ⟨(Kernel.id ×ₖ PY).map (timeChangeFamily Λ₀), ?_⟩
  filter_upwards [] with ω hω
  rw [Kernel.map_apply _ (measurable_timeChangeFamily d Λ₀), Kernel.prod_apply,
    Kernel.id_apply, Measure.dirac_prod,
    Measure.map_map (measurable_timeChangeFamily d Λ₀) measurable_prodMk_left]
  congr 1
  funext γ
  exact dite_eq_left hω

/-- For an arbitrary kernel, the same construction preserves all probability fibers.
This statement does not assert anything about the other input measures. -/
theorem c16_inverse_clock_quenched_family_on_probability_fibers
    (d : ℕ) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (PY : QuenchedPathLaws d) :
    ∃ PX : QuenchedPathLaws d, ∀ᵐ ω ∂Q.measure,
      ∀ hω : IsRegular Λ₀ ω, IsProbabilityMeasure (PY (0, ω)) →
        PX (0, ω) = Measure.map
          (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)
          (PY (0, ω)) := by
  classical
  let S : Set (Vec d × FieldPair d) := {a | PY a Set.univ = 1}
  have hS : MeasurableSet S :=
    measurableSet_eq_fun (Kernel.measurable_coe PY MeasurableSet.univ) measurable_const
  let PY₁ : QuenchedPathLaws d := Kernel.piecewise hS PY 0
  have : IsFiniteKernel PY₁ := by
    refine ⟨⟨1, ENNReal.one_lt_top, fun a => ?_⟩⟩
    simp only [PY₁, Kernel.piecewise_apply]
    split_ifs with h
    · exact h.le
    · simp
  refine ⟨(Kernel.id ×ₖ PY₁).map (timeChangeFamily Λ₀), ?_⟩
  filter_upwards [] with ω hω hprob
  have hmem : ((0 : Vec d), ω) ∈ S := measure_univ
  have h1 : PY₁ (0, ω) = PY (0, ω) := by
    simp only [PY₁, Kernel.piecewise_apply, hmem, ite_true]
  rw [Kernel.map_apply _ (measurable_timeChangeFamily d Λ₀), Kernel.prod_apply,
    Kernel.id_apply, Measure.dirac_prod, h1,
    Measure.map_map (measurable_timeChangeFamily d Λ₀) measurable_prodMk_left]
  congr 1
  funext γ
  exact dite_eq_left hω

/-- A reduced martingale-problem family admits jointly measurable inverse-clock
transport, since its origin fibers are probability measures almost everywhere. -/
theorem c16_inverse_clock_quenched_family_of_reduced_mp
    (d : ℕ) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ)
    (PY : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω))) :
    ∃ PX : QuenchedPathLaws d, ∀ᵐ ω ∂Q.measure,
      ∀ hω : IsRegular Λ₀ ω,
        PX (0, ω) = Measure.map
          (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω)
          (PY (0, ω)) := by
  obtain ⟨PX, hPX⟩ := c16_inverse_clock_quenched_family_on_probability_fibers
    d Λ₀ r₀ Q PY
  refine ⟨PX, ?_⟩
  filter_upwards [hPX, hY] with ω hPXω hYω
  intro hω
  exact hPXω hω hYω.1

end EinsteinFull
