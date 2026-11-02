import EinsteinFull.Calculus.S4KernelSupport
import EinsteinFull.Calculus.S4SharpDetSupport
import EinsteinFull.Frozen.ReducedLaw
import EinsteinFull.Frozen.SignedPhysicalFamily

/-!
# Force families for the sharp law, conditional on the draft well-posedness input

* `sharp_ae_smooth`: almost every environment of the sharp law is smooth (no structural data);
* `exists_forceFamilies`: from `svWellPosedStmt`, physical and reduced path-law families over all
  real forces related by the literal inverse clock (only almost-sure smoothness is used);
* `reduced_solution_ae_eq`: reduced solutions are unique, almost surely in the environment;
* the mean of the clock coordinate under the reduced law is the mean clock density.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.Blueprint
open EinsteinFull EinsteinRelation EinsteinRelation.Sharpness

theorem sharp_ae_smooth {d : ℕ} (hd : 2 ≤ d) {P : Measure (NoiseSample d)} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d))) :
    ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω := by
  rw [hQ]
  exact (ae_map_iff (EinsteinFull.Work.W8.measurable_physicalPair
    (⟨0, by omega⟩ : Fin d)).aemeasurable measurableSet_isSmoothFieldPair_fieldPair).mpr
    (ae_of_all P (EinsteinFull.Work.W8.physicalPair_isSmooth (⟨0, by omega⟩ : Fin d)))

theorem exists_forceFamilies {d : ℕ} (hwp : External.Draft.svWellPosedStmt) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω) (i : Fin d) :
    ∃ PX PY : DiffusionFamily d, IsSignedPhysicalFamily i Q PX ∧
      (∀ lam : ℝ, ∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY lam (0, ω))) ∧
      ∀ lam : ℝ, ∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular D.ellipticity ω,
        PX lam (0, ω) = (PY lam (0, ω)).map
          (fun γ : Path d => Clock.InverseMeaningV3.inverseClockPath ω γ D.ellipticity hω) := by
  have hΛ : 0 < D.ellipticity := lt_of_lt_of_le zero_lt_one D.one_le_ellipticity
  have h : ∀ lam : ℝ, ∃ PX PY : QuenchedPathLaws d,
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (physicalGenerator i ω lam) 0 (PX (0, ω))) ∧
      (∀ᵐ ω ∂Q.measure,
        SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (PY (0, ω))) := fun lam => by
    obtain ⟨PY, hM, hPY⟩ := exists_markov_kernel_reduced hwp hΛ i lam
    haveI := hM
    exact pathwiseV2_existence_part_of_kernel D Q hsm i lam PY hPY
  choose PX PY hX hY using h
  refine ⟨PX, PY, hX, hY, fun lam => ?_⟩
  filter_upwards [Q.regular, pathwiseV2_uniqueness_part hwp D Q hsm i lam (PX lam) (PY lam)
    (hX lam) (hY lam)] with ω hreg h
  exact ⟨hreg, (h hreg).1⟩

theorem reduced_solution_ae_eq {d : ℕ} (hwp : External.Draft.svWellPosedStmt) {Λ₀ r₀ : ℝ}
    (hΛ : 0 < Λ₀) (Q : EnvironmentLaw d Λ₀ r₀) (hsm : ∀ᵐ ω ∂Q.measure, IsSmoothFieldPair ω)
    (i : Fin d) (lam : ℝ) (Y Y' : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y (0, ω)))
    (hY' : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem (reducedGenerator i ω lam) 0 (Y' (0, ω))) :
    ∀ᵐ ω ∂Q.measure, Y (0, ω) = Y' (0, ω) := by
  filter_upwards [Q.regular, hsm, hY, hY'] with ω hreg hs h1 h2
  obtain ⟨P, _, hP⟩ := exists_unique_reduced_solution hwp hΛ hreg hs i lam 0
  exact (hP _ h1).trans (hP _ h2).symm

theorem reducedLaw_integral_clock {d : ℕ} {Λ₀ r₀ : ℝ} (Q : EnvironmentLaw d Λ₀ r₀) :
    ∫ ω, ω.2 (0 : Vec d) ∂reducedLaw Q = ∫ ω, clockDensity ω (0 : Vec d) ∂Q.measure := by
  have hc : Continuous fun ω : FieldPair d => ω.2 (0 : Vec d) :=
    (continuous_eval_const (0 : Vec d)).comp continuous_snd
  unfold reducedLaw
  rw [integral_map EinsteinRelation.Probability.measurable_reduce.aemeasurable
    hc.aestronglyMeasurable]
  rfl

end EinsteinFull.Blueprint
