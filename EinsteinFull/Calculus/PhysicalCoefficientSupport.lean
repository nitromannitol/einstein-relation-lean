import EinsteinRelation.Correctors.GTRegularCoefficientSupport
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic

open scoped ENNReal
open MeasureTheory
namespace EinsteinFull
open EinsteinRelation

/-- Uniform ellipticity and continuity put every coefficient entry in L infinity. -/
theorem memLp_complex_elliptic_entry {d : ℕ} (m : Measure (Vec d))
    (a : Vec d → Mat d) (Λ : ℝ) (hΛ : 0 < Λ) (ha : IsElliptic Λ a)
    (hc : ∀ j k, Continuous (fun x => a x j k)) (j k : Fin d) :
    MemLp (fun x => (a x j k : ℂ)) ∞ m := by
  apply memLp_top_of_bound
    ((Complex.continuous_ofReal.comp (hc j k)).aestronglyMeasurable) Λ
  exact Filter.Eventually.of_forall fun x => by
    simpa only [Function.comp_apply, Complex.norm_real, Real.norm_eq_abs] using
      Correctors.IsElliptic.entry_abs_le hΛ ha x j k

end EinsteinFull
