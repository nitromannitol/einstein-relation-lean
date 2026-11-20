import EinsteinFull.Homogenization.SourceResponseStationarity
import Homogenization.Book.Ch04.Theorems.Expectations

/-!
# Expected response partition defect

Stationarity turns the response partition defect in Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Lemma 2.13, into the difference of the expected responses at the two scales.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM

/-- The expected response defect is the difference of the expected response
at the descendant scale and at the parent scale. -/
theorem integral_sourceResponseDefect_eq_sub
    {d : ℕ} [NeZero d] {K : ℝ} (hK : 0 ≤ K)
    (P : Measure (Coefficient d K)) [IsProbabilityMeasure P]
    (hstat : ∀ z : LatticeIndex d, Measure.map (translateCoefficient (latticeShift z)) P = P)
    (Q : TriadicCube d) (j n : ℕ) (hscale : Q.scale = (n : ℤ) + j)
    (k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    (∫ a, descendantsAverage Q j (fun R => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
      (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q) -
      Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P) =
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
      (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P) -
    (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q ∂P) := by
  classical
  let X := fun R a => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
    (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q
  have hInt : Integrable (fun a => descendantsAverage Q j (fun R => X R a)) P := by
    have hs : Integrable (fun a => ∑ R ∈ descendantsAtDepth Q j, X R a) P :=
      integrable_finsetSum _ (fun R _ => integrable_sourceResponseJ_cube hK P R k hk p q)
    simpa only [descendantsAverage] using hs.const_mul (((descendantsAtDepth Q j).card : ℝ)⁻¹)
  rw [integral_sub hInt (integrable_sourceResponseJ_cube hK P Q k hk p q)]
  congr 1
  unfold descendantsAverage
  rw [integral_const_mul, integral_finsetSum _ (fun R _ =>
    integrable_sourceResponseJ_cube hK P R k hk p q)]
  have hn : ((descendantsAtDepth Q j).card : ℝ) ≠ 0 := by
    exact_mod_cast Finset.card_ne_zero.mpr (descendantsAtDepth_nonempty Q j)
  have hmean (R : TriadicCube d) (hR : R ∈ descendantsAtDepth Q j) :
      (∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q ∂P) =
      ∫ a, Book.Ch02.responseJ (Book.Ch02.cubeDomain (originCube d n))
        (sourceCoeffOn a (Book.Ch02.cubeDomain (originCube d n)) k hk) p q ∂P := by
    apply sourceResponseJ_expected_eq_origin hK P hstat R n ?_ k hk p q
    rw [scale_eq_sub_of_mem_descendantsAtDepth hR, hscale]
    simp
  rw [Finset.sum_congr rfl (fun R hR => hmean R hR), Finset.sum_const, nsmul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hn, one_mul]

end EinsteinFull.Homogenization
