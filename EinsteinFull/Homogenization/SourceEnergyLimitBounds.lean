import EinsteinFull.Homogenization.SourceEnergyAnnealed

/-!
# Bounds for the limiting annealed Dirichlet energy

The affine competitor bounds the expected Dirichlet energy and its limit in
Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Chapter 2.
-/

open MeasureTheory
open _root_.Homogenization
open EinsteinRelation (euclideanSq)

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The expected energy is integrable and bounded by the affine competitor. -/
theorem expected_sourceDirichletEnergy_bounds {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n : ℕ) (e : Vec d) :
    Integrable (fun a => sourceDirichletEnergy a (sourceTriadicCube d n) e) P ∧
      0 ≤ (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P) ∧
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P) ≤
        (K / 2) * euclideanSq e := by
  refine ⟨integrable_sourceDirichletEnergy hK P n e,
    expected_sourceDirichletEnergy_nonneg P n e, ?_⟩
  calc
    (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P) ≤
        ∫ _a, (K / 2) * euclideanSq e ∂P :=
      integral_mono (integrable_sourceDirichletEnergy hK P n e) (integrable_const _)
        (fun a => sourceDirichletEnergy_triadic_upper hK a n e)
    _ = (K / 2) * euclideanSq e := by simp

/-- The infimum of expected energies obeys the same affine bound. -/
theorem iInf_expected_sourceDirichletEnergy_bounds {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (e : Vec d) :
    0 ≤ (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P) ∧
      (⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P) ≤
        (K / 2) * euclideanSq e := by
  have hbelow : BddBelow (Set.range fun n : ℕ =>
      ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) e ∂P) := by
    refine ⟨0, ?_⟩
    rintro _ ⟨n, rfl⟩
    exact expected_sourceDirichletEnergy_nonneg P n e
  exact ⟨le_ciInf fun n => expected_sourceDirichletEnergy_nonneg P n e,
    (ciInf_le hbelow 0).trans (expected_sourceDirichletEnergy_bounds hK P 0 e).2.2⟩

end EinsteinFull.Homogenization
