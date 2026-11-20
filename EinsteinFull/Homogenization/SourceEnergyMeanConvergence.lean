import EinsteinFull.Homogenization.SubadditiveMeanConvergence
import EinsteinFull.Homogenization.SourceDualQuadratic

/-!
# Mean convergence of primal and dual energies

The primal and dual subadditive energies converge in mean under stationarity
and finite-range dependence. The primal result is the scalar part of
Proposition 1.7 of Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*; the dual result uses the same
argument through the response.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The Dirichlet energy converges in mean to its limiting expected value. -/
theorem tendsto_integral_abs_sourceDirichletEnergy_sub_limit
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (p : Vec d) :
    Tendsto (fun m : ℕ => ∫ a, |sourceDirichletEnergy a (sourceTriadicCube d m) p -
      (⨅ n : ℕ, ∫ b, sourceDirichletEnergy b (sourceTriadicCube d n) p ∂P)| ∂P)
      atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hk' : K ≤ (k : ℝ) + 1 := by linarith
  have hzero (a : Coefficient d K) (U : Book.Ch02.Domain d) :
      sourceDualEnergy a U 0 = 0 := by
    simpa using sourceDualEnergy_smul a U 0 (0 : Vec d)
  have h := tendsto_integral_abs_sourceResponseJ_sub_limit hK P hP hstat k hk' (-p) 0
  simp only [responseJ_eq_sourceDirichlet_add_sourceDual, neg_neg, hzero, add_zero,
    vecDot, Pi.zero_apply, mul_zero, Finset.sum_const_zero, sub_zero,
    integral_zero, ciInf_const, Book.Ch02.cubeDomain_coe,
    ← sourceTriadicCube_eq_openCubeSet] at h
  exact h

/-- The dual energy converges in mean to its limiting expected value. -/
theorem tendsto_integral_abs_sourceDualEnergy_sub_limit
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P] (hP : AKMFiniteRange P)
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (q : Vec d) :
    Tendsto (fun m : ℕ => ∫ a, |sourceDualEnergy a
      (Book.Ch02.cubeDomain (originCube d (m : ℤ))) q -
      (⨅ n : ℕ, ∫ b, sourceDualEnergy b
        (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P)| ∂P) atTop (𝓝 0) := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hk' : K ≤ (k : ℝ) + 1 := by linarith
  have hzero (a : Coefficient d K) (U : Book.Ch02.Domain d) :
      sourceDirichletEnergy a (U : Set (Vec d)) 0 = 0 := by
    simpa using sourceDirichletEnergy_smul a U 0 (0 : Vec d)
  have hzero' (a : Coefficient d K) (n : ℕ) :
      sourceDirichletEnergy a (sourceTriadicCube d n) 0 = 0 := by
    simpa only [Book.Ch02.cubeDomain_coe, ← sourceTriadicCube_eq_openCubeSet] using
      hzero a (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
  have h := tendsto_integral_abs_sourceResponseJ_sub_limit hK P hP hstat k hk' 0 q
  simp only [responseJ_eq_sourceDirichlet_add_sourceDual, neg_zero,
    vecDot, Pi.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero,
    Book.Ch02.cubeDomain_coe, ← sourceTriadicCube_eq_openCubeSet,
    hzero', integral_zero, ciInf_const, zero_add] at h
  exact h

end EinsteinFull.Homogenization
