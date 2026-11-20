import EinsteinFull.Homogenization.SourceResponseBridge
import Homogenization.Book.Ch02.Theorems.SubadditivityScaling

/-!
# Subadditivity of the Dirichlet energy

The Dirichlet energy of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, Chapter 2,
is subadditive over triadic partitions.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The source Dirichlet energy on a triadic domain is bounded by the weighted
average of the energies on a triadic partition. -/
theorem sourceDirichletEnergy_subadditive {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Book.Ch02.Domain d)
    (P : Book.Ch02.DomainPartition U) (e : Vec d) :
    EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) e ≤
      P.weightedAverage (fun i => EinsteinRelation.External.AKM.sourceDirichletEnergy a
        (P.cell i : Set (Vec d)) e) := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  have hrestr : ∀ i : P.Cell, Book.Ch02.CoeffOn.RestrictsTo
      (sourceCoeffOn a U k hK) (sourceCoeffOn a (P.cell i) k hK) := by
    intro i
    exact Filter.Eventually.of_forall fun _ => rfl
  have h := (Book.Ch02.responseSubadditivityAndScalingTheory U
    (sourceCoeffOn a U k hK)).responseJ_subadditive P
      (fun i => sourceCoeffOn a (P.cell i) k hK) hrestr (-e) 0
  have hvalue (V : Book.Ch02.Domain d) : Book.Ch02.responseJ V (sourceCoeffOn a V k hK)
      (-e) 0 = EinsteinRelation.External.AKM.sourceDirichletEnergy a (V : Set (Vec d)) e := by
    rw [Internal.Ch02.book_responseJ_eq_ResponseJ]
    exact (sourceDirichletEnergy_eq_ResponseJ a V k hK e).symm
  simpa only [hvalue] using h

end EinsteinFull.Homogenization
