import EinsteinFull.Homogenization.SourceDualBounds
import EinsteinFull.Homogenization.SourceDirichletTranslation
import Homogenization.Geometry.TriadicCubeTranslation

/-!
# Translation of dual energies

The dual energy of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, (2.1), is covariant under
simultaneous translation of domain and coefficient field.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The dual energy agrees with the block energy of the original coefficient. -/
theorem sourceDualEnergy_eq_Mu_original {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (q : Vec d) :
    sourceDualEnergy a U q = Mu (U : Set (Vec d)) (0, q) a.field := by
  rw [sourceDualEnergy_eq_Mu]
  exact Mu_congr_of_ae_eq (ae_restrict_of_ae (regularCoefficient_ae_eq a)) (0, q)

/-- Translating the domain is equivalent to translating the coefficient. -/
theorem sourceDualEnergy_translate {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U V : Book.Ch02.Domain d) (z q : Vec d)
    (hV : (V : Set (Vec d)) = translateSet z (U : Set (Vec d))) :
    sourceDualEnergy a V q = sourceDualEnergy (translateCoefficient z a) U q := by
  rw [sourceDualEnergy_eq_Mu_original, sourceDualEnergy_eq_Mu_original, hV,
    Mu_translateSet_eq_translateCoeffField]
  congr 1
  funext x
  simp [translateCoeffField, translateCoefficient, add_comm]
  congr 1

/-- Dual energies on a triadic cube are the centered-cube energies of the
translated coefficient. -/
theorem sourceDualEnergy_cube_eq_origin {d : ℕ} [NeZero d] {K : ℝ}
    (a : Coefficient d K) (Q : TriadicCube d) (q : Vec d) :
    sourceDualEnergy a (Book.Ch02.cubeDomain Q) q =
      sourceDualEnergy (translateCoefficient (triadicCubeShift Q) a)
        (Book.Ch02.cubeDomain (originCube d Q.scale)) q := by
  apply sourceDualEnergy_translate
  exact openCubeSet_eq_translateSet_originCube_of_triadicCube Q

/-- The dual energy on any triadic cube is nonnegative and uniformly bounded. -/
theorem sourceDualEnergy_cube_bounds {d : ℕ} [NeZero d] {K : ℝ}
    (a : Coefficient d K) (Q : TriadicCube d) (q : Vec d) :
    0 ≤ sourceDualEnergy a (Book.Ch02.cubeDomain Q) q ∧
      sourceDualEnergy a (Book.Ch02.cubeDomain Q) q ≤ vecNormSq q := by
  rw [sourceDualEnergy_cube_eq_origin]
  exact sourceDualEnergy_originCube_bounds _ _ _

/-- The dual energy on any triadic cube is integrable under a finite law. -/
theorem integrable_sourceDualEnergy_cube {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P] (Q : TriadicCube d) (q : Vec d) :
    Integrable (fun a => sourceDualEnergy a (Book.Ch02.cubeDomain Q) q) P := by
  apply (integrable_const (vecNormSq q)).mono'
    (measurable_sourceDualEnergy_cube_full Q q).aestronglyMeasurable
  exact ae_of_all _ fun a => by
    rw [Real.norm_of_nonneg (sourceDualEnergy_cube_bounds a Q q).1]
    exact (sourceDualEnergy_cube_bounds a Q q).2

end EinsteinFull.Homogenization
