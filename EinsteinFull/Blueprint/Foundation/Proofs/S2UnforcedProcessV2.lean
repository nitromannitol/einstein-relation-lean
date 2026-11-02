import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopePathwise
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeUnforced
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeRealSemigroup
import EinsteinFull.Blueprint.Foundation.node_stationary_u2D_environment
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds
import EinsteinFull.Calculus.S2QuenchedSemigroupFamily
import EinsteinFull.Calculus.U3UnforcedResolventIdentification
import EinsteinFull.Calculus.SunaS8ForceNormalization

open MeasureTheory
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinRelation EinsteinFull

/-- Smooth-scope version of `QuenchedSemigroupFamilyStmt`: one reduced quenched family realizing the
actual complex `L²` evolution, for every structural datum `D` and smooth environment law `Q`
(`HasSmoothBounds D Q`). -/
def QuenchedSemigroupFamilyStmtV2 : Prop :=
  ∀ (d : ℕ), 2 ≤ d → ∀ (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange),
    HasSmoothBounds D Q → ∀ (i : Fin d) (lam : ℝ),
    ∃ Y : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω))) ∧
      ∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)), ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
        forcedComplexEvolution Q i (lam : ℂ) t f (reduce ω) =
          ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω)

/-- Any two reduced solutions have the same origin quenched law for a.e. environment, from the
smooth-scope pathwise node. -/
theorem reducedOriginLaw_ae_unique_of_pathwiseV2
    (hpath : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (i : Fin d) (lam : ℝ) (Y Y' : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (hY' : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator i ω lam) 0
      (Y' (0, ω))) :
    ∀ᵐ ω ∂Q.measure, Y (0, ω) = Y' (0, ω) := by
  obtain ⟨⟨PX, PY, hPX, _⟩, huniq⟩ := hpath d hd D Q hQ i lam
  have h1 := huniq PX Y hPX hY
  have h2 := huniq PX Y' hPX hY'
  refine originLaw_ae_eq_of_inverseClock Q PX Y Y' ?_ ?_
  · filter_upwards [h1] with ω h hω
    exact (h hω).1
  · filter_upwards [h2] with ω h hω
    exact (h hω).1

/-- The path clause for an arbitrary reduced solution, from the smooth-scope pathwise node and one
realizing family. -/
theorem pathClause_of_familyV2
    (hpath : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    (hfam : QuenchedSemigroupFamilyStmtV2)
    {d : ℕ} (hd : 2 ≤ d) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange) (hQ : HasSmoothBounds D Q)
    (i : Fin d) (lam : ℝ) :
    ∀ Y : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω))) →
      ∀ (t : ℝ≥0) (f : Lp ℂ 2 (reducedLaw Q)), ∀ᵐ ω ∂Q.measure,
        Integrable (fun γ : Path d => f (translate (γ t) (reduce ω))) (Y (0, ω)) ∧
        forcedComplexEvolution Q i (lam : ℂ) t f (reduce ω) =
          ∫ γ : Path d, f (translate (γ t) (reduce ω)) ∂Y (0, ω) := by
  obtain ⟨Y0, hY0, hid⟩ := hfam d hd D Q hQ i lam
  intro Y hY t f
  have huniq := reducedOriginLaw_ae_unique_of_pathwiseV2 hpath hd D Q hQ i lam Y0 Y hY0 hY
  filter_upwards [huniq, hid t f] with ω he hω
  rw [← he]
  exact hω

/-- `stationary-environment#unforced-process`, smooth-scope version. The non-path clauses are the
all-`Q` lemmas for the actual zero-force evolution. For the path clause, the smooth pathwise node
gives the relation at `Q`; the canonical origin kernel then realizes the evolution on bounded tests,
and uniqueness of the reduced origin law transfers this to every solution. The other two graph
premises are retained in their prescribed order. -/
@[nolint unusedArguments]
theorem node_stationary_u2D_environment_u23_unforced_u2D_process_of_deps
    (hpath : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    (_hstat : node_stationary_u2D_environmentStmt)
    (_hbounds : node_eq_u2E_reduced_u2D_boundsStmt) :
    node_stationary_u2D_environment_u23_unforced_u2D_processStmtV2 := by
  intro d hd D Q hQ i
  have hP : PathwiseAt Q := hpath d hd D Q hQ
  obtain ⟨K, hmarkov, hK, hunique⟩ := exists_c2UnforcedOriginKernel Q hP i
  let : ProbabilityTheory.IsMarkovKernel K := hmarkov
  refine ⟨forcedComplexEvolution Q i 0,
    isComplexEnvironmentSemigroup_forcedComplexEvolution Q i 0,
    isComplexTransposeSemigroup_forcedComplexEvolution_zero Q i,
    fun t f => ⟨norm_forcedComplexEvolution_zero_apply_le Q i t f,
      integral_forcedComplexEvolution_zero Q i t f⟩,
    fun f => forcedComplexEvolution_zero_fixed_iff Q hd i f,
    fun f G hG h => exists_const_of_zero_energy Q hd f G hG h, ?_⟩
  intro Y hY t f
  have hp := c2Unforced_path_identity_of_bounded_tests Q i K
    (u3_unforced_markov_kernel_bounded_test_identity hd Q hP K hK) t f
  filter_upwards [hp, hunique Y hY] with ω hp he
  rw [← he]
  exact hp

/-- `e:generators#real-semigroup`, smooth-scope version. The generator clauses hold for every
environment law. For the path clause, the smooth unforced-process and pathwise nodes give their
relations at `Q`, and the supplied signed-force action then agrees with the actual evolution on
bounded continuous tests. -/
theorem node_e_u3A_generators_u23_real_u2D_semigroup_of_deps
    (hunforced : node_stationary_u2D_environment_u23_unforced_u2D_processStmtV2)
    (hpath : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2) :
    node_e_u3A_generators_u23_real_u2D_semigroupStmtV2 := by
  intro d hd D Q hQ lam i P Pdag
  obtain ⟨h1, h2, h3, h4⟩ := realForce_semigroup_clauses Q i lam
  refine ⟨h1, h2, h3, h4, ?_⟩
  intro Y hY t f
  have hi : External.GantertSection7Support.firstCoordinateIndex hd = (⟨0, by omega⟩ : Fin d) :=
    Fin.ext rfl
  refine u3_real_force_quenched_action_of_bounded_tests hd Q lam Y hY t (fun g F hF => ?_) f
  have h := s8_supplied_signed_bounded_endpoint_eq_evolution hd Q (hunforced d hd D Q hQ)
    (hpath d hd D Q hQ) lam Y (by simpa only [hi] using hY) g F hF t
  rw [hi] at h
  exact h

end EinsteinFull.Blueprint
