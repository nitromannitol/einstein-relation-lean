import EinsteinFull.Homogenization.SourceDualTranslation
import EinsteinFull.Homogenization.SourceDualSubadditivity
import EinsteinFull.Homogenization.SourceEnergyStationarity

/-!
# Annealed dual energies

Subadditivity and stationarity imply convergence of the expected dual energies
in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic Homogenization and
Large-Scale Regularity*, Chapter 2.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- Stationarity makes expected dual energies independent of position at each
nonnegative triadic scale. -/
theorem sourceDualEnergy_expected_eq_origin {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (n : ℕ) (hscale : Q.scale = n) (q : Vec d) :
    (∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain Q) q ∂P) =
      ∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P := by
  let z : LatticeIndex d := fun i => Q.index i * (3 : ℤ) ^ n
  let U := Book.Ch02.cubeDomain (originCube d (n : ℤ))
  let f : Coefficient d K → ℝ := fun a => sourceDualEnergy a U q
  have hf : Integrable f P := integrable_sourceDualEnergy_originCube P n q
  have hmp : MeasurePreserving (translateCoefficient (latticeShift z)) P P :=
    ⟨measurable_translateCoefficient _, hP z⟩
  have hpoint (a : Coefficient d K) : sourceDualEnergy a (Book.Ch02.cubeDomain Q) q =
      f (translateCoefficient (latticeShift z) a) := by
    apply sourceDualEnergy_translate
    change openCubeSet Q = translateSet (latticeShift z) (openCubeSet (originCube d (n : ℤ)))
    simpa only [sourceTriadicCube_eq_openCubeSet] using
      openCubeSet_eq_latticeTranslate_sourceTriadicCube Q n hscale
  calc
    (∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain Q) q ∂P) =
        ∫ a, f (translateCoefficient (latticeShift z) a) ∂P :=
          integral_congr_ae (ae_of_all _ hpoint)
    _ = ∫ a, f a ∂P := by
      have hmap := integral_map (measurable_translateCoefficient (latticeShift z)).aemeasurable
        (by rw [hmp.map_eq]; exact hf.aestronglyMeasurable)
      rw [hmp.map_eq] at hmap
      exact hmap.symm

/-- Expected dual energy decreases between successive triadic scales. -/
theorem expected_sourceDualEnergy_succ_le {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (q : Vec d) (n : ℕ) :
    (∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) q ∂P) ≤
      ∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P := by
  classical
  let Q := originCube d ((n + 1 : ℕ) : ℤ)
  let D := descendantsAtDepth Q 1
  let F : Coefficient d K → TriadicCube d → ℝ := fun a R =>
    sourceDualEnergy a (Book.Ch02.cubeDomain R) q
  have hF (R : TriadicCube d) : Integrable (fun a => F a R) P :=
    integrable_sourceDualEnergy_cube P R q
  have hsum : Integrable (fun a => ∑ R ∈ D, F a R) P :=
    integrable_finsetSum D (fun R _ => hF R)
  have havg : Integrable (fun a => descendantsAverage Q 1 (F a)) P := by
    simpa [descendantsAverage, D] using hsum.const_mul ((D.card : ℝ)⁻¹)
  have hbound := integral_mono (hF Q) havg
    (fun a => sourceDualEnergy_le_descendantsAverage a Q 1 q)
  have hchild (R : TriadicCube d) (hR : R ∈ D) :
      (∫ a, F a R ∂P) = ∫ a, F a (originCube d (n : ℤ)) ∂P := by
    have hs := scale_eq_sub_of_mem_descendantsAtDepth hR
    have hs' : R.scale = (n : ℤ) := by dsimp [D, Q, originCube] at hs; omega
    exact sourceDualEnergy_expected_eq_origin P hP R n hs' q
  have havg_eq : (∫ a, descendantsAverage Q 1 (F a) ∂P) =
      ∫ a, F a (originCube d (n : ℤ)) ∂P := by
    change (∫ a, (D.card : ℝ)⁻¹ * ∑ R ∈ D, F a R ∂P) = _
    rw [integral_const_mul, integral_finsetSum D (fun R _ => hF R)]
    have hD : (D.card : ℝ) ≠ 0 := by
      exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q 1)
    have heq : (∑ R ∈ D, ∫ a, F a R ∂P) =
        D.card * (∫ a, F a (originCube d (n : ℤ)) ∂P) := by
      rw [Finset.sum_congr rfl hchild, Finset.sum_const, nsmul_eq_mul]
    rw [heq, ← mul_assoc, inv_mul_cancel₀ hD, one_mul]
  rw [havg_eq] at hbound
  exact hbound

/-- Expected dual energies converge to their infimum over triadic scales. -/
theorem tendsto_expected_sourceDualEnergy {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (q : Vec d) :
    Tendsto (fun n : ℕ => ∫ a, sourceDualEnergy a
      (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P) atTop
      (𝓝 (⨅ n : ℕ, ∫ a, sourceDualEnergy a
        (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P)) := by
  apply tendsto_atTop_ciInf (antitone_nat_of_succ_le (expected_sourceDualEnergy_succ_le P hP q))
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact integral_nonneg fun a => (sourceDualEnergy_originCube_bounds a n q).1

end EinsteinFull.Homogenization
