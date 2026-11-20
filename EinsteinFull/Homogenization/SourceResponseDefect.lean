import EinsteinFull.Homogenization.SourceResponseLocality
import Homogenization.Book.Ch05.Theorems.Section53.JUpperBoundWeakNorms.Additivity.ParentRestriction

/-!
# Response partition defect

The second-variation identity in Lemma 2.12 of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, relates
response energy defects to differences of maximizer gradients.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport
open EinsteinRelation.External.AKM
open Book.Ch05.Section53.JUpperBoundWeakNorms

/-- The regular representative of a source coefficient is locally a.e. elliptic. -/
theorem regularCoefficient_locallyElliptic {d : ℕ} {K : ℝ}
    (a : Coefficient d K) : Book.Ch04.AELocallyUniformlyEllipticField
      (regularCoefficient a) := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  intro Q
  let A := unitLowerSourceCoeffOn a (Book.Ch02.cubeDomain Q) k hK
  refine ⟨1, (k : ℝ) + 1, zero_lt_one, by linarith [Nat.cast_nonneg (α := ℝ) k], ?_⟩
  simpa [A, unitLowerSourceCoeffOn, Book.Ch04.AEEllipticOn,
    Book.Ch02.cubeDomain_coe] using ch02_coeffOn_isAEEllipticFieldOn A

/-- The dependent regular-coefficient family and the source coefficient have
identical response values on every triadic cube. -/
theorem responseJ_regularCoefficient_eq_source {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (Q : TriadicCube d) (k : ℕ)
    (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      ((Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
        (regularCoefficient a) (regularCoefficient_locallyElliptic a)).coeffOn Q) p q =
    Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
      (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q := by
  apply Book.Ch02.responseJ_eq_ofAEEq
  exact Filter.EventuallyEq.rfl

/-- The descendant average of the half-energy of maximizer-gradient differences
is the source response partition defect. -/
theorem descendantsAverage_sourceResponseDifferenceEnergy_eq_defect
    {d : ℕ} [NeZero d] {K : ℝ} (a : Coefficient d K)
    (Q : TriadicCube d) (j k : ℕ) (hk : K ≤ (k : ℝ) + 1) (p q : Vec d) :
    let F := Book.Ch04.triadicCoeffFamilyOfAELocallyUniformlyEllipticField
      (regularCoefficient a) (regularCoefficient_locallyElliptic a)
    descendantsAverage Q j
        (fun R => cubeAverage R (additivityDiffHalfEnergyDensityOnFamilyOnCube F Q R p q)) =
      descendantsAverage Q j (fun R => Book.Ch02.responseJ (Book.Ch02.cubeDomain R)
        (sourceCoeffOn a (Book.Ch02.cubeDomain R) k hk) p q) -
      Book.Ch02.responseJ (Book.Ch02.cubeDomain Q)
        (sourceCoeffOn a (Book.Ch02.cubeDomain Q) k hk) p q := by
  intro F
  rw [descendantsAverage_additivityDiffHalfEnergyOnDependentFamily_eq_responseJPartitionDefectOnFamilyAtDepth]
  unfold responseJPartitionDefectOnFamilyAtDepth childResponseJAverageOnFamilyAtDepth
  simp_rw [responseJ_regularCoefficient_eq_source a _ k hk p q]

end EinsteinFull.Homogenization
