import EinsteinFull.Homogenization.SourceEnergyAnnealed
import EinsteinFull.Homogenization.SourceDirichletQuadratic

/-!
# Quadraticity of annealed Dirichlet energies

Averaging the quadratic Dirichlet energy of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
preserves its homogeneity and parallelogram identity.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- Expected Dirichlet energies are homogeneous of degree two. -/
theorem expected_sourceDirichletEnergy_smul {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (n : ℕ) (c : ℝ) (e : Vec d) :
    Integrable (fun a => EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) (c • e)) P ∧
    (∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) (c • e) ∂P) =
    c ^ 2 * ∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) e ∂P := by
  refine ⟨integrable_sourceDirichletEnergy hK P n (c • e), ?_⟩
  have hpoint (a : Coefficient d K) : EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) (c • e) =
      c ^ 2 * EinsteinRelation.External.AKM.sourceDirichletEnergy a
        (EinsteinRelation.External.AKM.sourceTriadicCube d n) e := by
    simpa [sourceTriadicCube_eq_openCubeSet] using
      sourceDirichletEnergy_smul a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) c e
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ hpoint)

/-- Expected Dirichlet energies satisfy the parallelogram identity. -/
theorem expected_sourceDirichletEnergy_parallelogram {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (n : ℕ) (e₁ e₂ : Vec d) :
    (∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) (e₁ + e₂) ∂P) +
    (∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) (e₁ - e₂) ∂P) =
    2 * (∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) e₁ ∂P) +
    2 * (∫ a, EinsteinRelation.External.AKM.sourceDirichletEnergy a
      (EinsteinRelation.External.AKM.sourceTriadicCube d n) e₂ ∂P) := by
  have hpoint (a : Coefficient d K) :=
    sourceDirichletEnergy_parallelogram a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) e₁ e₂
  have h := integral_congr_ae (ae_of_all P hpoint)
  simp only [Book.Ch02.cubeDomain_coe, ← sourceTriadicCube_eq_openCubeSet] at h
  rw [integral_add (integrable_sourceDirichletEnergy hK P n (e₁ + e₂))
      (integrable_sourceDirichletEnergy hK P n (e₁ - e₂)),
    integral_add ((integrable_sourceDirichletEnergy hK P n e₁).const_mul 2)
      ((integrable_sourceDirichletEnergy hK P n e₂).const_mul 2),
    integral_const_mul, integral_const_mul] at h
  exact h

end EinsteinFull.Homogenization
