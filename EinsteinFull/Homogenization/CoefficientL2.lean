import EinsteinFull.Homogenization.CoefficientCarrier
import Homogenization.Book.Ch04.Internal.AEESliceAssembly.CarrierMuFamily

/-!
# Local coefficient realizations in L²

For the coefficient fields of Armstrong, Kuusi and Mourrat,
*Quantitative Stochastic Homogenization and Large-Scale Regularity*, (0.6)–(0.11),
local smooth observations determine a measurable matrix-valued L² realization.
-/

open MeasureTheory

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Environment.AKMTestIntegralSupport

/-- The regular coefficient has a locally measurable L² realization on every
finite-volume open set on which it belongs to a quantitative ellipticity slice. -/
theorem measurable_regularCoefficient_toHilbertMatrixL2 {d : ℕ} {K : ℝ}
    (U : Set (Vec d)) [IsFiniteMeasure (_root_.Homogenization.volumeMeasureOn U)]
    (hU : IsOpen U) (k : ℕ)
    (hslice : ∀ a : Coefficient d K,
      _root_.Homogenization.AEEQuantitativeEllipticSlice U k (regularCoefficient a).toFun) :
    @Measurable (Coefficient d K)
      (Lp (_root_.Homogenization.HilbertMat d) 2 (_root_.Homogenization.volumeMeasureOn U))
      (localSigma U) (borel _)
      (fun a => _root_.Homogenization.AEEQuantitativeEllipticSlice.toHilbertMatrixL2
        (_root_.Homogenization.rawSlice regularCoefficient hslice a)) := by
  have hfinite : volume U ≠ ⊤ := isFiniteMeasure_restrict.mp inferInstance
  apply _root_.Homogenization.measurable_toHilbertMatrixL2_carrier hU.measurableSet
    (hUopen := hU) (hUfinite := hfinite)
  intro i j φ hφ hφc hφU
  exact measurable_entryTestR_regularCoefficient U ⟨φ, hφ, hφc⟩ hφU i j

end EinsteinFull.Homogenization
