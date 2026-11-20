import EinsteinFull.Homogenization.SourceEnergyAnnealedQuadratic
import EinsteinFull.Homogenization.SourceDirichletPolar

/-!
# Polarization of annealed Dirichlet energy

Averaging the Dirichlet energy from Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
preserves the bilinearity of its polarization.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The polarization of expected Dirichlet energy is additive in its first argument. -/
theorem expected_sourceDirichletEnergy_polar_add_left {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (n : ℕ) (x y z : Vec d) :
    (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (x + y + z) ∂P) -
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (x + y) ∂P) -
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) z ∂P) =
    ((∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (x + z) ∂P) -
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) x ∂P) -
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) z ∂P)) +
    ((∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (y + z) ∂P) -
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) y ∂P) -
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) z ∂P)) := by
  let F : Vec d → Coefficient d K → ℝ := fun e a =>
    sourceDirichletEnergy a (sourceTriadicCube d n) e
  have hF (e : Vec d) : Integrable (F e) P := integrable_sourceDirichletEnergy hK P n e
  have hp (a : Coefficient d K) : F (x + y + z) a - F (x + y) a - F z a =
      (F (x + z) a - F x a - F z a) + (F (y + z) a - F y a - F z a) := by
    simpa [F, sourceTriadicCube_eq_openCubeSet] using
      sourceDirichletEnergy_polar_add_left a
        (Book.Ch02.cubeDomain (originCube d (n : ℤ))) x y z
  have hi := integral_congr_ae (ae_of_all P hp)
  have hleft : (∫ a, F (x + y + z) a - F (x + y) a - F z a ∂P) =
      (∫ a, F (x + y + z) a ∂P) - (∫ a, F (x + y) a ∂P) - ∫ a, F z a ∂P := by
    calc
      _ = (∫ a, F (x + y + z) a - F (x + y) a ∂P) - ∫ a, F z a ∂P :=
        integral_sub ((hF (x + y + z)).sub (hF (x + y))) (hF z)
      _ = _ := by rw [integral_sub (hF (x + y + z)) (hF (x + y))]
  have hthree (u v w : Vec d) : (∫ a, F u a - F v a - F w a ∂P) =
      (∫ a, F u a ∂P) - (∫ a, F v a ∂P) - ∫ a, F w a ∂P := by
    calc
      _ = (∫ a, F u a - F v a ∂P) - ∫ a, F w a ∂P :=
        integral_sub ((hF u).sub (hF v)) (hF w)
      _ = _ := by rw [integral_sub (hF u) (hF v)]
  have hright : (∫ a, (F (x + z) a - F x a - F z a) +
      (F (y + z) a - F y a - F z a) ∂P) =
      (∫ a, F (x + z) a - F x a - F z a ∂P) +
      ∫ a, F (y + z) a - F y a - F z a ∂P :=
    integral_add (((hF (x + z)).sub (hF x)).sub (hF z))
      (((hF (y + z)).sub (hF y)).sub (hF z))
  rw [hleft, hright, hthree, hthree] at hi
  exact hi

/-- The polarization of expected Dirichlet energy is homogeneous in its first argument. -/
theorem expected_sourceDirichletEnergy_polar_smul_left {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (n : ℕ) (c : ℝ) (x y : Vec d) :
    (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (c • x + y) ∂P) -
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (c • x) ∂P) -
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) y ∂P) =
    c * ((∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (x + y) ∂P) -
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) x ∂P) -
      (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) y ∂P)) := by
  let F : Vec d → Coefficient d K → ℝ := fun e a =>
    sourceDirichletEnergy a (sourceTriadicCube d n) e
  have hF (e : Vec d) : Integrable (F e) P := integrable_sourceDirichletEnergy hK P n e
  have hp (a : Coefficient d K) : F (c • x + y) a - F (c • x) a - F y a =
      c * (F (x + y) a - F x a - F y a) := by
    simpa [F, sourceTriadicCube_eq_openCubeSet] using
      sourceDirichletEnergy_polar_smul_left a
        (Book.Ch02.cubeDomain (originCube d (n : ℤ))) c x y
  have hi := integral_congr_ae (ae_of_all P hp)
  have hthree (u v w : Vec d) : (∫ a, F u a - F v a - F w a ∂P) =
      (∫ a, F u a ∂P) - (∫ a, F v a ∂P) - ∫ a, F w a ∂P := by
    calc
      _ = (∫ a, F u a - F v a ∂P) - ∫ a, F w a ∂P :=
        integral_sub ((hF u).sub (hF v)) (hF w)
      _ = _ := by rw [integral_sub (hF u) (hF v)]
  rw [hthree, integral_const_mul, hthree] at hi
  exact hi

end EinsteinFull.Homogenization
