import EinsteinFull.Homogenization.QuadraticSumBound
import EinsteinFull.Homogenization.SourceEnergyAnnealedQuadratic
import EinsteinFull.Homogenization.SourceDualQuadratic

/-!
# Summability of uniform response decrements

The response decrements of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, Chapter 2, are
controlled uniformly in the loadings by finitely many energy decrements.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The decrease in expected Dirichlet energy between consecutive scales. -/
noncomputable def sourceDirichletDecrement {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) (n : ℕ) (p : Vec d) : ℝ :=
  (∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) p ∂P) -
    ∫ a, sourceDirichletEnergy a (sourceTriadicCube d (n + 1)) p ∂P

/-- The decrease in expected dual energy between consecutive scales. -/
noncomputable def sourceDualDecrement {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) (n : ℕ) (q : Vec d) : ℝ :=
  (∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P) -
    ∫ a, sourceDualEnergy a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) q ∂P

/-- Dirichlet-energy decrements are nonnegative under stationarity. -/
theorem sourceDirichletDecrement_nonneg {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (n : ℕ) (p : Vec d) : 0 ≤ sourceDirichletDecrement P n p :=
  sub_nonneg.mpr (expected_sourceDirichletEnergy_succ_le hK P hstat p n)

/-- Dual-energy decrements are nonnegative under stationarity. -/
theorem sourceDualDecrement_nonneg {d : ℕ} [NeZero d] {K : ℝ}
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (n : ℕ) (q : Vec d) : 0 ≤ sourceDualDecrement P n q :=
  sub_nonneg.mpr (expected_sourceDualEnergy_succ_le P hstat q n)

/-- The response decrement splits into the primal and dual energy decrements. -/
theorem expected_sourceResponseJ_decrement_eq {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P) -
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d ((n + 1 : ℕ) : ℤ))) k hk) p q ∂P) =
    sourceDirichletDecrement P n (-p) + sourceDualDecrement P n q := by
  rw [expected_sourceResponseJ_eq hK P n k hk p q,
    expected_sourceResponseJ_eq hK P (n + 1) k hk p q]
  dsimp only [sourceDirichletDecrement, sourceDualDecrement]
  ring

/-- The uniform response decrement is bounded by coordinate energy decrements. -/
theorem sourceResponseTau_le_sum_decrements {d : ℕ} [NeZero d] {K : ℝ}
    (hK : 0 ≤ K) (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (n k : ℕ) (hk : K ≤ (k : ℝ) + 1) :
    sourceResponseTau P n k hk ≤ (2 : ℝ) ^ d *
      ∑ i : Fin d, (sourceDirichletDecrement P n (Pi.single i 1) +
        sourceDualDecrement P n (Pi.single i 1)) := by
  have hDpar (x y : Vec d) : sourceDirichletDecrement P n (x + y) +
      sourceDirichletDecrement P n (x - y) =
      2 * sourceDirichletDecrement P n x + 2 * sourceDirichletDecrement P n y := by
    have h₁ := expected_sourceDirichletEnergy_parallelogram hK P n x y
    have h₂ := expected_sourceDirichletEnergy_parallelogram hK P (n + 1) x y
    dsimp only [sourceDirichletDecrement]
    linarith
  have hDsmul (c : ℝ) (x : Vec d) : sourceDirichletDecrement P n (c • x) =
      c ^ 2 * sourceDirichletDecrement P n x := by
    dsimp only [sourceDirichletDecrement]
    rw [(expected_sourceDirichletEnergy_smul hK P n c x).2,
      (expected_sourceDirichletEnergy_smul hK P (n + 1) c x).2]
    ring
  have hQpar (x y : Vec d) : sourceDualDecrement P n (x + y) +
      sourceDualDecrement P n (x - y) =
      2 * sourceDualDecrement P n x + 2 * sourceDualDecrement P n y := by
    have h₁ := expected_sourceDualEnergy_parallelogram P n x y
    have h₂ := expected_sourceDualEnergy_parallelogram P (n + 1) x y
    dsimp only [sourceDualDecrement]
    linarith
  have hQsmul (c : ℝ) (x : Vec d) : sourceDualDecrement P n (c • x) =
      c ^ 2 * sourceDualDecrement P n x := by
    dsimp only [sourceDualDecrement]
    rw [expected_sourceDualEnergy_smul P n c x,
      expected_sourceDualEnergy_smul P (n + 1) c x]
    ring
  apply csSup_le (sourceResponseDecrementValues_nonempty P n k hk)
  rintro z ⟨p, q, hp, hq, rfl⟩
  rw [expected_sourceResponseJ_decrement_eq hK P n k hk p q]
  have hp' (i : Fin d) : (-p i) ^ 2 ≤ 1 := by
    have hi := sq_apply_le_vecNormSq p i
    nlinarith
  have hq' (i : Fin d) : q i ^ 2 ≤ 1 := by
    have hi := sq_apply_le_vecNormSq q i
    linarith
  have h₁ := quadratic_le_sum_single (sourceDirichletDecrement P n)
    (sourceDirichletDecrement_nonneg hK P hstat n) hDpar hDsmul (-p) hp'
  have h₂ := quadratic_le_sum_single (sourceDualDecrement P n)
    (sourceDualDecrement_nonneg P hstat n) hQpar hQsmul q hq'
  simp only [Fintype.card_fin] at h₁ h₂
  rw [Finset.sum_add_distrib, mul_add]
  linarith

end EinsteinFull.Homogenization
