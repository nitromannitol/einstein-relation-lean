import EinsteinFull.Homogenization.SourceResponseBridge
import Homogenization.Book.Ch02.Theorems.Quadraticity

/-!
# Quadraticity of the Dirichlet energy

The Dirichlet energy in Armstrong, Kuusi and Mourrat, *Quantitative Stochastic
Homogenization and Large-Scale Regularity*, Chapter 2, is a quadratic function
of the prescribed affine gradient.
-/

open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The Dirichlet energy is homogeneous of degree two in the loading. -/
theorem sourceDirichletEnergy_smul {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (c : ℝ) (e : Vec d) :
    EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) (c • e) =
      c ^ 2 * EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) e := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  have hvalue (v : Vec d) : Book.Ch02.responseJ U (sourceCoeffOn a U k hK) (-v) 0 =
      EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) v := by
    rw [Internal.Ch02.book_responseJ_eq_ResponseJ]
    exact (sourceDirichletEnergy_eq_ResponseJ a U k hK v).symm
  have h := Book.Ch02.responseJ_smul (a := sourceCoeffOn a U k hK) c (-e) 0
  simpa only [smul_zero, smul_neg, hvalue] using h

/-- The Dirichlet energy satisfies the parallelogram identity. -/
theorem sourceDirichletEnergy_parallelogram {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (e₁ e₂ : Vec d) :
    EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) (e₁ + e₂) +
      EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) (e₁ - e₂) =
    2 * EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) e₁ +
      2 * EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) e₂ := by
  obtain ⟨k, hk⟩ := exists_nat_ge K
  have hK : K ≤ (k : ℝ) + 1 := by linarith
  have hvalue (v : Vec d) : Book.Ch02.responseJ U (sourceCoeffOn a U k hK) (-v) 0 =
      EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) v := by
    rw [Internal.Ch02.book_responseJ_eq_ResponseJ]
    exact (sourceDirichletEnergy_eq_ResponseJ a U k hK v).symm
  have h := Book.Ch02.responseJ_parallelogram (a := sourceCoeffOn a U k hK) (-e₁) 0 (-e₂) 0
  simp only [zero_add, sub_self] at h
  rw [show -e₁ + -e₂ = -(e₁ + e₂) by abel,
    show -e₁ - -e₂ = -(e₁ - e₂) by abel, hvalue (e₁ + e₂),
    hvalue (e₁ - e₂), hvalue e₁, hvalue e₂] at h
  exact h

end EinsteinFull.Homogenization
