import EinsteinFull.Homogenization.OpenCubeEnergyMeasurability
import Homogenization.Book.Ch02.Theorems.DeterministicIdentities

/-!
# Dirichlet and response energies

The Dirichlet energy and the response quantity of Armstrong, Kuusi and
Mourrat, *Quantitative Stochastic Homogenization and Large-Scale Regularity*,
Chapter 2, agree at zero flux with opposite potential loading.
-/

open MeasureTheory
open _root_.Homogenization

namespace EinsteinFull.Homogenization

open EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The source coefficient as an almost-everywhere elliptic Chapter 2
coefficient on an open bounded convex domain. -/
noncomputable def sourceCoeffOn {d : ℕ} {K : ℝ} (a : Coefficient d K)
    (U : Book.Ch02.Domain d) (k : ℕ) (hK : K ≤ (k : ℝ) + 1) : Book.Ch02.CoeffOn U := by
  have hEll := regularCoefficient_aeeQuantitativeEllipticSlice (U : Set (Vec d))
    U.measurableSet k hK a
  have hone : (1 : ℝ) ≤ (k : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) k]
  have hpos : (0 : ℝ) < (k : ℝ) + 1 := lt_of_lt_of_le zero_lt_one hone
  exact { toCoeffField := (regularCoefficient a).toFun
          lam := ((k : ℝ) + 1)⁻¹
          Lam := (k : ℝ) + 1
          lam_pos := inv_pos.mpr hpos
          lam_le_Lam := ((inv_le_one₀ hpos).2 hone).trans hone
          aeStronglyMeasurable := hEll.2.1
          aeElliptic := hEll.2.2 }

/-- The source Dirichlet energy equals the Chapter 2 response with negative
potential loading and zero flux loading. -/
theorem sourceDirichletEnergy_eq_ResponseJ {d : ℕ} {K : ℝ}
    (a : Coefficient d K) (U : Book.Ch02.Domain d) (k : ℕ)
    (hK : K ≤ (k : ℝ) + 1) (e : Vec d) :
    EinsteinRelation.External.AKM.sourceDirichletEnergy a (U : Set (Vec d)) e =
      ResponseJ (U : Set (Vec d)) (-e) 0 (sourceCoeffOn a U k hK).toCoeffField := by
  rw [sourceDirichletEnergy_eq_Mu_regularCoefficient a U.isOpen e]
  have h := Book.Ch02.ResponseJ_eq_Mu_neg_left_sub_vecDot U (sourceCoeffOn a U k hK) (-e) 0
  simpa [sourceCoeffOn, vecDot] using h.symm

end EinsteinFull.Homogenization
