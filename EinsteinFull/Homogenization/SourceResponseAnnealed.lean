import EinsteinFull.Homogenization.SourceEnergyDuality

/-!
# Annealed response

The response in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Chapter 2, is integrable on
triadic cubes and its expectation converges under a stationary law.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The response on a triadic cube is integrable under a finite law. -/
theorem integrable_sourceResponseJ {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsFiniteMeasure P] (n k : ℕ)
    (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    Integrable (fun a => Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q) P := by
  have h := ((integrable_sourceDirichletEnergy hK P n (-p)).add
    (integrable_sourceDualEnergy_originCube P n q)).sub (integrable_const (vecDot p q))
  convert h using 1
  funext a
  rw [responseJ_eq_sourceDirichlet_add_sourceDual]
  rw [Book.Ch02.cubeDomain_coe, ← sourceTriadicCube_eq_openCubeSet]
  rfl

/-- The expected response splits into the two expected energies and the pairing. -/
theorem expected_sourceResponseJ_eq {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (n k : ℕ)
    (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P) =
    (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (-p) ∂P) +
      (∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P) -
        vecDot p q := by
  simp_rw [responseJ_eq_sourceDirichlet_add_sourceDual, Book.Ch02.cubeDomain_coe,
    ← sourceTriadicCube_eq_openCubeSet]
  have hab : Integrable (fun a => sourceDirichletEnergy a (sourceTriadicCube d n) (-p) +
      sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q) P := by
    exact (integrable_sourceDirichletEnergy hK P n (-p)).add
      (integrable_sourceDualEnergy_originCube P n q)
  rw [integral_sub hab (integrable_const _),
    integral_add (integrable_sourceDirichletEnergy hK P n (-p))
      (integrable_sourceDualEnergy_originCube P n q)]
  simp only [integral_const, probReal_univ, one_smul]

/-- Expected responses converge to the sum of the limiting energies minus the pairing. -/
theorem tendsto_expected_sourceResponseJ {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hP : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    Tendsto (fun n : ℕ => ∫ a, Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P)
      atTop (𝓝 ((⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (-p) ∂P) +
        (⨅ n : ℕ, ∫ a, sourceDualEnergy a
          (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P) - vecDot p q)) := by
  have h := ((tendsto_expected_sourceDirichletEnergy hK P hP (-p)).add
    (tendsto_expected_sourceDualEnergy P hP q)).sub (tendsto_const_nhds (x := vecDot p q))
  refine h.congr' (Filter.Eventually.of_forall fun n => ?_)
  exact (expected_sourceResponseJ_eq hK P n k hk p q).symm

end EinsteinFull.Homogenization
