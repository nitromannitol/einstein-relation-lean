import EinsteinRelation.External.AKMEnergyDensitySources
import Mathlib.Topology.Order.MonotoneConvergence

/-!
# Lower bounds for the source Dirichlet energies

Source: `paper/main.tex:693-698,727-729`; AKM (1.7), printed p. 5,
and the bounded monotone limit argument (1.21)--(1.22), pp. 10--11.
These results use the literal zero-boundary class and Dirichlet infimum.
The convergence result explicitly retains the unproved monotonicity premise.
-/

open MeasureTheory Filter Topology
noncomputable section
namespace EinsteinRelation.External.AKM
open Environment.AKMTestIntegralSupport

/-- The zero function is an admissible zero-boundary variation on any domain. -/
theorem sourceH01_zero {d : ℕ} (U : Set (Vec d)) :
    SourceH01 U (fun _ => 0) (fun _ => 0) := by
  refine ⟨MemLp.zero, MemLp.zero, ?_, fun _ _ => 0, ?_, ?_, ?_⟩
  · intro i
    refine ⟨locallyIntegrableOn_zero, locallyIntegrableOn_zero, ?_⟩
    intro φ hφ
    simp
  · intro n
    exact ⟨contDiff_const, HasCompactSupport.zero, by simp⟩
  · simp
  · simp [gradient, coordinateDerivative, euclideanSq, dot]

/-- Ellipticity makes every admissible Dirichlet energy nonnegative. -/
theorem sourceDirichletEnergy_nonneg {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Set (Vec d)) (e : Vec d) : 0 ≤ sourceDirichletEnergy a U e := by
  apply Real.sInf_nonneg
  rintro E ⟨u, g, hu, rfl⟩
  unfold average
  apply integral_nonneg
  intro x
  have hs : 0 ≤ euclideanSq (e + g x) := by
    unfold euclideanSq dot
    exact Finset.sum_nonneg fun i _ => mul_self_nonneg ((e + g x) i)
  exact mul_nonneg (by norm_num) (hs.trans (a.elliptic x _).1)

/-- At zero loading the zero variation realizes the energy infimum. -/
theorem sourceDirichletEnergy_zero {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Set (Vec d)) : sourceDirichletEnergy a U 0 = 0 := by
  apply le_antisymm _ (sourceDirichletEnergy_nonneg a U 0)
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro E ⟨u, g, hu, rfl⟩
    unfold average
    apply integral_nonneg
    intro x
    have hs : 0 ≤ euclideanSq ((0 : Vec d) + g x) := by
      unfold euclideanSq dot
      exact Finset.sum_nonneg fun i _ => mul_self_nonneg (((0 : Vec d) + g x) i)
    exact mul_nonneg (by norm_num) (hs.trans (a.elliptic x _).1)
  · exact ⟨fun _ => 0, fun _ => 0, sourceH01_zero U, by simp [dot]⟩

/-- Expectations retain the lower bound without any extra measurability premise. -/
theorem expected_sourceDirichletEnergy_nonneg {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K)) (n : ℕ) (e : Vec d) :
    0 ≤ ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P :=
  integral_nonneg fun a => sourceDirichletEnergy_nonneg a _ e

/-- Once (1.21) is proved, (1.22) follows from the established lower bound.
This is a conditional internal reduction, not a proof of subadditivity. -/
theorem tendsto_expected_sourceDirichletEnergy_of_antitone {d : ℕ} {K : ℝ}
    (P : Measure (Coefficient d K)) (e : Vec d)
    (hmono : Antitone (fun n : ℕ =>
      ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P)) :
    Tendsto (fun n : ℕ => ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P)
      atTop (𝓝 (⨅ n : ℕ, ∫ a,
        sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P)) := by
  apply tendsto_atTop_ciInf hmono
  refine ⟨0, ?_⟩
  rintro x ⟨n, rfl⟩
  exact expected_sourceDirichletEnergy_nonneg P n e

end EinsteinRelation.External.AKM
