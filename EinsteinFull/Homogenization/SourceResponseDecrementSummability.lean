import EinsteinFull.Homogenization.SourceResponseDecrement
import EinsteinFull.Homogenization.SourceResponseAnnealed

/-!
# Summability of response decrements

For fixed loadings, the expected response decrements of Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 2, telescope to the difference between the initial and limiting
expected energies.
-/

open MeasureTheory Filter Topology
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- Fixed-loading expected response decrements are nonnegative and sum to
the difference between the initial expected response and its limit. -/
theorem hasSum_expected_sourceResponseJ_decrement
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    let F := fun n : ℕ => ∫ a, Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q ∂P
    (∀ n : ℕ, Integrable (fun a => Book.Ch02.responseJ
      (Book.Ch02.cubeDomain (originCube d (n : ℤ)))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d (n : ℤ))) k hk) p q) P) ∧
    (∀ n, 0 ≤ F n - F (n + 1)) ∧
    HasSum (fun n => F n - F (n + 1))
      (F 0 - ((⨅ n : ℕ, ∫ a, sourceDirichletEnergy a (sourceTriadicCube d n) (-p) ∂P) +
        (⨅ n : ℕ, ∫ a, sourceDualEnergy a
          (Book.Ch02.cubeDomain (originCube d (n : ℤ))) q ∂P) - vecDot p q)) := by
  intro F
  refine ⟨fun n => integrable_sourceResponseJ hK P n k hk p q, ?_, ?_⟩
  · intro n
    dsimp only [F]
    rw [expected_sourceResponseJ_eq hK P n k hk p q,
      expected_sourceResponseJ_eq hK P (n + 1) k hk p q]
    have hp := expected_sourceDirichletEnergy_succ_le hK P hstat (-p) n
    have hq := expected_sourceDualEnergy_succ_le P hstat q n
    linarith
  · rw [hasSum_iff_tendsto_nat_of_nonneg]
    · have ht := tendsto_expected_sourceResponseJ hK P hstat k hk p q
      change Tendsto F atTop _ at ht
      have ht' := (tendsto_const_nhds (x := F 0)).sub ht
      refine ht'.congr' (Eventually.of_forall fun n => ?_)
      have hsum := Finset.sum_range_sub F n
      simp only [Finset.sum_sub_distrib] at hsum
      dsimp only
      rw [Finset.sum_sub_distrib]
      linarith
    · intro n
      dsimp only [F]
      rw [expected_sourceResponseJ_eq hK P n k hk p q,
        expected_sourceResponseJ_eq hK P (n + 1) k hk p q]
      have hp := expected_sourceDirichletEnergy_succ_le hK P hstat (-p) n
      have hq := expected_sourceDualEnergy_succ_le P hstat q n
      linarith

end EinsteinFull.Homogenization
