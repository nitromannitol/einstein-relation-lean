import EinsteinFull.Homogenization.SourceEnergyMatrixConvergence
import EinsteinFull.Homogenization.SourceResponseBridge
import Homogenization.CoarseGraining.CoarseBounds.Sandwich
import Homogenization.Internal.Ch02.Representatives

/-!
# Coercivity of source Dirichlet energy

The Dirichlet energy in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Chapter 2, controls the squared
magnitude of its affine loading uniformly over triadic scales.
-/

open MeasureTheory
open _root_.Homogenization
open EinsteinRelation (euclideanSq)

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The source coefficient with its unit lower ellipticity bound on a domain. -/
noncomputable def unitLowerSourceCoeffOn {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (k : ℕ) (hK : K ≤ (k : ℝ) + 1) : Book.Ch02.CoeffOn U where
  toCoeffField := (regularCoefficient a).toFun
  lam := 1
  Lam := (k : ℝ) + 1
  lam_pos := zero_lt_one
  lam_le_Lam := by linarith [Nat.cast_nonneg (α := ℝ) k]
  aeStronglyMeasurable := (sourceCoeffOn a U k hK).aeStronglyMeasurable
  aeElliptic := by
    filter_upwards [ae_restrict_of_ae (regularCoefficient_ae_eq a)] with x hx
    rw [hx]
    exact source_isEllipticMatrix a (by linarith [Nat.cast_nonneg (α := ℝ) k]) hK x

/-- Source Dirichlet energy has a uniform positive lower bound on triadic cubes. -/
theorem sourceDirichletEnergy_triadic_lower {d : ℕ} [NeZero d] {K : ℝ}
    (a : Coefficient d K) (n : ℕ) (e : Vec d) :
    (1 / 4 : ℝ) * euclideanSq e ≤ sourceDirichletEnergy a (sourceTriadicCube d n) e := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  let Q := originCube d (n : ℤ)
  let U := Book.Ch02.cubeDomain Q
  let A := unitLowerSourceCoeffOn a U k hK
  let A' := Internal.Ch02.BookCh02.pointwiseCoeffField U A
  have hEll : IsEllipticFieldOn 1 ((k : ℝ) + 1) (cubeSet Q) A' :=
    Internal.Ch02.BookCh02.pointwiseCoeffField_isEllipticFieldOn_cubeSet Q A
  have hbound := diag_lower_le_mu_cube hEll (e, 0)
  have hU : IsOpen (sourceTriadicCube d n) := by
    rw [sourceTriadicCube_eq_openCubeSet]
    exact isOpen_openCubeSet _
  let : IsFiniteMeasure (volumeMeasureOn (sourceTriadicCube d n)) := by
    rw [sourceTriadicCube_eq_openCubeSet]
    simpa [volumeMeasureOn] using
      (isOpenBoundedConvexDomain_openCubeSet Q).isFiniteMeasure_restrict_volume
  have hae : A' =ᵐ[volumeMeasureOn (sourceTriadicCube d n)] (regularCoefficient a).toFun := by
    simpa [A', A, U, Q, unitLowerSourceCoeffOn, sourceTriadicCube_eq_openCubeSet] using
      Internal.Ch02.BookCh02.pointwiseCoeffField_ae_eq U A
  have heq : Mu (cubeSet Q) (e, 0) A' = sourceDirichletEnergy a (sourceTriadicCube d n) e := by
    rw [← Mu_sourceTriadicCube_eq_cubeSet n (e, 0) A',
      Mu_congr_of_ae_eq hae (e, 0), ← sourceDirichletEnergy_eq_Mu_regularCoefficient a hU e]
  rw [heq] at hbound
  simpa [vecNormSq, euclideanSq, EinsteinRelation.dot, vecDot] using hbound

end EinsteinFull.Homogenization
