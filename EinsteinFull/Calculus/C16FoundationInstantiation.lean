import EinsteinFull.Calculus.S4ReducedCoefficientSupport
import EinsteinFull.Calculus.S4KernelSupport
import EinsteinFull.Calculus.C4TextbookFoundation
import EinsteinFull.Calculus.C16ReducedMPExistence
import EinsteinFull.Calculus.C21OccupationUniformIntegrability

/-!
# Instantiating the announced diffusion foundation for the actual reduced coefficient

The coefficient and drift hypotheses are proved in `S4ReducedCoefficientSupport`.
The admitted textbook foundation now supplies well-posedness directly.
This gives the textbook operator; transferring to the divergence-form reduced generator
still requires occupation control of the exceptional set of spatial derivatives.
-/

namespace EinsteinFull

open EinsteinRelation MeasureTheory ProbabilityTheory
open scoped NNReal

/-- The announced textbook foundation applies to the anisotropic reduced coefficient
of every regular environment, with arbitrary signed force and every starting point. -/
theorem foundation_reduced_textbook_well_posed
    {d : ℕ} (hd : 1 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) (x : Vec d) :
    ∃! P : Measure (Path d), SolvesMartingaleProblem
      (External.Draft.svGenerator (reducedCoefficient ω)
        (forcedDrift (reducedCoefficient ω) i lam)) x P := by
  obtain ⟨hc, hs, hb, he, hm, hbd⟩ := reduced_svHypotheses hΛ hω i lam
  exact foundation_textbook_well_posed d hd (reducedCoefficient ω)
    (forcedDrift (reducedCoefficient ω) i lam) hc hs hb he hm hbd x

/-- The textbook foundation supplies a jointly measurable probability kernel of
textbook reduced solutions on every regular environment. The existing measurable
solution relation and unique-selection construction require no smoothness assumption. -/
theorem foundation_reduced_textbook_kernel
    {d : ℕ} {Λ₀ : ℝ} (hΛ : 0 < Λ₀) (i : Fin d) (lam : ℝ) :
    ∃ PY : QuenchedPathLaws d, IsMarkovKernel PY ∧
      ∀ ω : FieldPair d, IsRegular Λ₀ ω →
        SolvesMartingaleProblem
          (External.Draft.svGenerator (reducedCoefficient ω)
            (forcedDrift (reducedCoefficient ω) i lam)) 0 (PY (0, ω)) := by
  obtain ⟨g, hg, hgs⟩ :=
    exists_family_solution_kernel foundation_textbook_well_posed hΛ i lam
  let PY : QuenchedPathLaws d := ⟨fun a => g a.2, hg.comp measurable_snd⟩
  refine ⟨PY, ⟨fun a => (hgs a.2).1⟩, ?_⟩
  intro ω hω
  have hP := (hgs ω).2
  rw [famA_eq_of_regular hω, famB_eq_of_regular i lam hω] at hP
  exact hP

/-- A supplied-law occupation estimate transfers the measurable textbook kernel
to the actual reduced martingale problem. -/
theorem c16_reduced_mp_exists_of_averaged_occupation
    (d : ℕ) (Λ₀ r₀ : ℝ) (Q : EnvironmentLaw d Λ₀ r₀)
    (i : Fin d) (lam : ℝ)
    (hocc : ∀ (ω : FieldPair d), IsRegular Λ₀ ω →
      ∀ (P : Measure (Path d)),
        SolvesMartingaleProblem (External.Draft.svGenerator (reducedCoefficient ω)
          (forcedDrift (reducedCoefficient ω) i lam)) 0 P →
        Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
          (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d))) :
    ∃ PY : QuenchedPathLaws d, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω)) := by
  have hΛ : 0 < Λ₀ := lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter
  obtain ⟨PY, _, hPY⟩ := foundation_reduced_textbook_kernel hΛ i lam
  refine ⟨PY, ?_⟩
  filter_upwards [Q.regular] with ω hω
  exact c16_reduced_solves_of_textbook_and_averaged_occupation hΛ hω i lam
    (hPY ω hω) (hocc ω hω (PY (0, ω)) (hPY ω hω))

/-- In dimension at least two the supplied textbook law has absolutely
continuous positive-time averaged occupation measure. -/
theorem foundation_reduced_textbook_averaged_occupation_ac_of_two_le {d : ℕ}
    (hd : 2 ≤ d) {Λ₀ : ℝ} (hΛ : 0 < Λ₀) {ω : FieldPair d}
    (hω : IsRegular Λ₀ ω) (i : Fin d) (lam : ℝ) {x : Vec d}
    {P : Measure (Path d)}
    (hP : SolvesMartingaleProblem (External.Draft.svGenerator
      (reducedCoefficient ω) (forcedDrift (reducedCoefficient ω) i lam)) x P) :
    Measure.map (fun z : Path d × ℝ => z.1 z.2.toNNReal)
      (P.prod (volume.restrict (Set.Ioi 0))) ≪ (volume : Measure (Vec d)) := by
  letI : IsProbabilityMeasure P := hP.1
  apply c21_averaged_occupation_ac_of_finite_null P
  intro N hN hnull n
  simpa using c21_textbook_null_occupation_finite hd hΛ hω i lam hP hN hnull (n : ℝ≥0)

/-- The actual reduced martingale problem has a measurable family of solutions
in dimension at least two. -/
theorem c16_reduced_mp_exists (d : ℕ) (hd : 2 ≤ d) (Λ₀ r₀ : ℝ)
    (Q : EnvironmentLaw d Λ₀ r₀) (i : Fin d) (lam : ℝ) :
    ∃ PY : QuenchedPathLaws d, ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω)) := by
  apply c16_reduced_mp_exists_of_averaged_occupation d Λ₀ r₀ Q i lam
  intro ω hω P hP
  exact foundation_reduced_textbook_averaged_occupation_ac_of_two_le hd
    (lt_of_lt_of_le zero_lt_one Q.ellipticity_parameter) hω i lam hP


/-- A measurable Markov kernel solving the actual reduced martingale problem
on every regular environment. -/
theorem foundation_reduced_actual_kernel {d : ℕ} (hd : 2 ≤ d)
    {Λ₀ : ℝ} (hΛ : 0 < Λ₀) (i : Fin d) (lam : ℝ) :
    ∃ PY : QuenchedPathLaws d, IsMarkovKernel PY ∧
      ∀ ω : FieldPair d, IsRegular Λ₀ ω →
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω)) := by
  obtain ⟨PY, hmarkov, hPY⟩ := foundation_reduced_textbook_kernel hΛ i lam
  refine ⟨PY, hmarkov, ?_⟩
  intro ω hω
  exact c16_reduced_solves_of_textbook_and_averaged_occupation hΛ hω i lam
    (hPY ω hω)
    (foundation_reduced_textbook_averaged_occupation_ac_of_two_le hd hΛ hω i lam
      (hPY ω hω))

end EinsteinFull
