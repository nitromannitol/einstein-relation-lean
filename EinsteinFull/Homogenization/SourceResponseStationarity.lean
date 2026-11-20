import EinsteinFull.Homogenization.SourceResponseVariance

/-!
# Stationary response averages

The response energies in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Chapter 2, have position-independent
expectations on cubes of the same nonnegative triadic scale.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The expectation of the response on a cube splits into the expected
Dirichlet and dual energies and the pairing. -/
theorem expected_sourceResponseJ_cube_eq {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (Q : TriadicCube d)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P) =
    (∫ a, sourceDirichletEnergy a (openCubeSet Q) (-p) ∂P) +
      (∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain Q) q ∂P) - vecDot p q := by
  simp_rw [responseJ_eq_sourceDirichlet_add_sourceDual, Book.Ch02.cubeDomain_coe]
  have hab : Integrable (fun a => sourceDirichletEnergy a (openCubeSet Q) (-p) +
      sourceDualEnergy a (Book.Ch02.cubeDomain Q) q) P :=
    (integrable_sourceDirichletEnergy_openCube hK P Q (-p)).add
      (integrable_sourceDualEnergy_cube P Q q)
  rw [integral_sub hab (integrable_const _),
    integral_add (integrable_sourceDirichletEnergy_openCube hK P Q (-p))
      (integrable_sourceDualEnergy_cube P Q q)]
  simp only [integral_const, probReal_univ, one_smul]

/-- Stationarity makes expected responses independent of the cube position at
nonnegative triadic scales. -/
theorem sourceResponseJ_expected_eq_origin {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (n : ℕ) (hscale : Q.scale = n)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P) =
    ∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P := by
  rw [expected_sourceResponseJ_cube_eq hK P Q k hk p q,
    expected_sourceResponseJ_eq hK P n k hk p q,
    sourceDirichletEnergy_expected_eq_origin hK P hP Q n hscale (-p),
    sourceDualEnergy_expected_eq_origin P hP Q n hscale q]

/-- Averaging responses over nonempty cubes at a common nonnegative scale
preserves their common expectation. -/
theorem expected_average_sourceResponseJ_eq_origin {ι : Type*} [Fintype ι]
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : ι → TriadicCube d) (n : ℕ) (S : Finset ι) (hS : S.Nonempty)
    (hscale : ∀ i ∈ S, (Q i).scale = n)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    (∫ a, (S.card : ℝ)⁻¹ * ∑ i ∈ S,
      Book.Ch02.responseJ (Book.Ch02.cubeDomain (Q i))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk) p q ∂P) =
    ∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P := by
  classical
  rw [integral_const_mul, integral_finsetSum S (fun i _ =>
    integrable_sourceResponseJ_cube hK P (Q i) k hk p q)]
  have hn : (S.card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr hS
  have heq : (∑ i ∈ S, ∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (Q i))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (Q i)) k hk) p q ∂P) =
      (S.card : ℝ) * (∫ a, Book.Ch02.responseJ
        (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P) := by
    rw [Finset.sum_congr rfl (fun i hi =>
      sourceResponseJ_expected_eq_origin hK P hP (Q i) n (hscale i hi) k hk p q),
      Finset.sum_const, nsmul_eq_mul]
  rw [heq, ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end EinsteinFull.Homogenization
