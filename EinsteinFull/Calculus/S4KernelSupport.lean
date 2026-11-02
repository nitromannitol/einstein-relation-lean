import EinsteinFull.Calculus.S4CoefficientFamilySupport
import EinsteinFull.Calculus.S4PolishSupport
import EinsteinFull.Calculus.S4MeasureSelectionSupport
import EinsteinFull.Calculus.S4PathwiseV2Support
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopePathwise

/-!
# `pathwiseV2_of_svWellPosed`

The draft well-posedness input implies the smooth-scope pathwise statement `V2`: well-posedness
of every member of the coefficient family, measurability of the solution relation, the measurable
selection theorem, the Markov kernel of reduced solutions, and the clock identity.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal Classical

namespace EinsteinFull
open EinsteinRelation

theorem famA_eq_of_regular {d : ℕ} {Λ : ℝ} {ω : FieldPair d} (hreg : IsRegular Λ ω) :
    famA Λ ω = reducedCoefficient ω :=
  funext fun y => by
    unfold famA
    rw [if_pos hreg]

theorem famB_eq_of_regular {d : ℕ} {Λ : ℝ} {ω : FieldPair d} (i : Fin d) (lam : ℝ)
    (hreg : IsRegular Λ ω) : famB Λ i lam ω = forcedDrift (reducedCoefficient ω) i lam :=
  funext fun y => by
    unfold famB
    rw [if_pos hreg]

theorem family_wellPosed {d : ℕ} (hwp : External.Draft.svWellPosedStmt) {Λ : ℝ} (hΛ : 0 < Λ)
    (i : Fin d) (lam : ℝ) (ω : FieldPair d) :
    ∃! P : Measure (Path d), SolvesMartingaleProblem
      (External.Draft.svGenerator (famA Λ ω) (famB Λ i lam ω)) 0 P := by
  by_cases hreg : IsRegular Λ ω
  · rw [famA_eq_of_regular hreg, famB_eq_of_regular i lam hreg]
    exact exists_unique_clean_reduced_solution hwp hΛ hreg i lam 0
  · have e1 : famA Λ ω = fun _ => 1 := funext fun y => by
      unfold famA
      rw [if_neg hreg]
    have e2 : famB Λ i lam ω = fun _ => 0 := funext fun y => by
      unfold famB
      rw [if_neg hreg]
    rw [e1, e2]
    refine hwp d (Fin.pos i) (fun _ => 1) (fun _ => 0) continuous_const
      (fun _ => Matrix.transpose_one) ⟨1, fun _ a b => ?_⟩ ⟨1, one_pos, fun x ξ => ?_⟩
      measurable_const ⟨0, fun _ k => by simp⟩ 0
    · rcases eq_or_ne a b with rfl | hab
      · simp
      · simp [Matrix.one_apply, hab]
    · simp [euclideanSq, Matrix.one_mulVec]

theorem exists_family_solution_kernel {d : ℕ} (hwp : External.Draft.svWellPosedStmt) {Λ : ℝ}
    (hΛ : 0 < Λ) (i : Fin d) (lam : ℝ) :
    ∃ g : FieldPair d → Measure (Path d), Measurable g ∧ ∀ ω, IsProbabilityMeasure (g ω) ∧
      SolvesMartingaleProblem
        (External.Draft.svGenerator (famA Λ ω) (famB Λ i lam ω)) 0 (g ω) := by
  letI : PolishSpace (FieldPair d) := fieldPair_polish d
  obtain ⟨M, hAb, hBb⟩ := family_bounds hΛ i lam
  have hR := measurableSet_solutionRelation (famA Λ) (famB Λ i lam)
    (fun a b => measurable_famA Λ a b) (fun k => measurable_famB Λ i lam k)
    (fun θ y a b => hAb θ y a b) (fun θ y k => hBb θ y k) 0
  obtain ⟨g, hg, hgR⟩ := exists_measurable_selector_measure
    (fun (ω : FieldPair d) (P : Measure (Path d)) => SolvesMartingaleProblem
      (External.Draft.svGenerator (famA Λ ω) (famB Λ i lam ω)) 0 P)
    (fun ω P h => h.1) (family_wellPosed hwp hΛ i lam) hR
  exact ⟨g, hg, fun ω => ⟨(hgR ω).1, hgR ω⟩⟩

theorem exists_markov_kernel_reduced {d : ℕ} (hwp : External.Draft.svWellPosedStmt) {Λ : ℝ}
    (hΛ : 0 < Λ) (i : Fin d) (lam : ℝ) :
    ∃ PY : QuenchedPathLaws d, IsMarkovKernel PY ∧
      ∀ ω : FieldPair d, IsRegular Λ ω → IsSmoothFieldPair ω →
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω)) := by
  obtain ⟨g, hg, hgs⟩ := exists_family_solution_kernel hwp hΛ i lam
  let PY : QuenchedPathLaws d := ⟨fun a => g a.2, hg.comp measurable_snd⟩
  haveI : IsMarkovKernel PY := ⟨fun a => (hgs a.2).1⟩
  refine ⟨PY, inferInstance, fun ω hreg hsm => ?_⟩
  have h := (hgs ω).2
  rw [famA_eq_of_regular hreg, famB_eq_of_regular i lam hreg] at h
  exact (reducedGenerator_solves_iff hsm i lam 0 (g ω)).2 h

end EinsteinFull

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation

/-- The draft textbook input implies the smooth-scope pathwise statement. -/
theorem pathwiseV2_of_svWellPosed (hwp : External.Draft.svWellPosedStmt) :
    node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2 := by
  intro d _ D Q hs i lam
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one D.one_le_ellipticity
  have hs' : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω := hs.mono fun ω h => h.1
  refine ⟨?_, fun PX PY hX hY => pathwiseV2_uniqueness_part hwp D Q hs' i lam PX PY hX hY⟩
  obtain ⟨PY, hM, hPY⟩ := exists_markov_kernel_reduced hwp hΛ i lam
  haveI := hM
  exact pathwiseV2_existence_part_of_kernel D Q hs' i lam PY hPY

end EinsteinFull.Blueprint
