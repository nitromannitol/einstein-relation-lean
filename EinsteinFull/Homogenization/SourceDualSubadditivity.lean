import EinsteinFull.Homogenization.SourceDualBlockBridge
import Homogenization.Book.Ch02.Theorems.SubadditivityScaling
import Homogenization.Book.Ch02.Theorems.HomogenizationError.ResponseBounds

/-!
# Subadditivity of the dual energy

The dual energy in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, (2.1), is subadditive over
partitions into admissible domains.
-/

open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The dual energy on a domain is bounded by the weighted average of the dual
energies on a partition. -/
theorem sourceDualEnergy_subadditive {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Book.Ch02.Domain d)
    (P : Book.Ch02.DomainPartition U) (q : Vec d) :
    sourceDualEnergy a U q ≤ P.weightedAverage (fun i => sourceDualEnergy a (P.cell i) q) := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  have hrestr : ∀ i : P.Cell, Book.Ch02.CoeffOn.RestrictsTo
      (sourceCoeffOn a U k hK) (sourceCoeffOn a (P.cell i) k hK) := by
    intro i
    exact Filter.Eventually.of_forall fun _ => rfl
  have h := (Book.Ch02.responseSubadditivityAndScalingTheory U
    (sourceCoeffOn a U k hK)).responseJ_subadditive P
      (fun i => sourceCoeffOn a (P.cell i) k hK) hrestr 0 q
  have hvalue (V : Book.Ch02.Domain d) : Book.Ch02.responseJ V (sourceCoeffOn a V k hK)
      0 q = sourceDualEnergy a V q := by
    have hsplit := responseJ_eq_sourceDirichlet_add_sourceDual a V k hK 0 q
    have hzero : EinsteinRelation.External.AKM.sourceDirichletEnergy a (V : Set (Vec d)) 0 = 0 := by
      simpa using sourceDirichletEnergy_smul a V 0 (0 : Vec d)
    simpa [hzero, vecDot] using hsplit
  simpa only [hvalue] using h

/-- Subadditivity on a triadic cube in terms of its descendants at a fixed
finite depth. -/
theorem sourceDualEnergy_le_descendantsAverage {d : ℕ} [NeZero d] {K : ℝ}
    (a : Coefficient d K) (Q : TriadicCube d) (j : ℕ) (q : Vec d) :
    sourceDualEnergy a (Book.Ch02.cubeDomain Q) q ≤
      descendantsAverage Q j (fun R => sourceDualEnergy a (Book.Ch02.cubeDomain R) q) := by
  have h := sourceDualEnergy_subadditive a (Book.Ch02.cubeDomain Q)
    (Book.Ch02.descendantsDomainPartition Q j) q
  change sourceDualEnergy a (Book.Ch02.cubeDomain Q) q ≤
    (Book.Ch02.descendantsDomainPartition Q j).weightedAverage (fun i =>
      sourceDualEnergy a (Book.Ch02.cubeDomain i.1) q) at h
  rw [Book.Ch02.descendantsDomainPartition_weightedAverage Q j
    (fun R => sourceDualEnergy a (Book.Ch02.cubeDomain R) q)] at h
  exact h

end EinsteinFull.Homogenization
