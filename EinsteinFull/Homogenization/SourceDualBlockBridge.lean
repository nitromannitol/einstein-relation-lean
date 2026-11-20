import EinsteinFull.Homogenization.SourceDualEnergy
import EinsteinFull.Homogenization.SourceDirichletQuadratic

/-!
# Dual and block energies

The Neumann quantity in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, (2.1), agrees with the doubled
variational energy at zero potential loading.
-/

open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The dual energy equals the doubled energy at zero potential loading. -/
theorem sourceDualEnergy_eq_Mu {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (q : Vec d) :
    sourceDualEnergy a U q = Mu (U : Set (Vec d)) (0, q) (regularCoefficient a).toFun := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  have hzero : EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) 0 = 0 := by
    simpa using sourceDirichletEnergy_smul a U 0 (0 : Vec d)
  have hsplit := responseJ_eq_sourceDirichlet_add_sourceDual a U k hK 0 q
  have hMu := Book.Ch02.ResponseJ_eq_Mu_neg_left_sub_vecDot U (sourceCoeffOn a U k hK) 0 q
  rw [Internal.Ch02.book_responseJ_eq_ResponseJ] at hsplit
  simp only [neg_zero, hzero, zero_add, vecDot, Pi.zero_apply, zero_mul,
    Finset.sum_const_zero, sub_zero] at hsplit hMu
  rw [← hsplit, hMu]
  rfl

end EinsteinFull.Homogenization
