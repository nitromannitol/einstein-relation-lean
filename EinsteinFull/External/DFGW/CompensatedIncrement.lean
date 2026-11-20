import EinsteinFull.External.DFGW.Trajectory
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

/-! # Shifted compensated increments

The compensated increment over a later interval is the initial compensated increment on the
shifted trajectory, provided the drift is integrable on the adjacent intervals.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- A compensated later increment is the shifted initial compensated increment. -/
theorem compensated_increment_eq_shift (hX : Draft.IsDFGWTrajectoryFamily P X Y)
    (φ : S → Vec d) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b)
    (hint : ∀ᵐ η ∂P, IntervalIntegrable (fun t => φ (η t)) volume 0 a ∧
      IntervalIntegrable (fun t => φ (η t)) volume a b) :
    (fun η => (X 0 b η - ∫ t in (0 : ℝ)..b, φ (η t)) -
      (X 0 a η - ∫ t in (0 : ℝ)..a, φ (η t))) =ᵐ[P]
    (fun η => X 0 (b - a) (Draft.dfgwShift a η) -
      ∫ t in (0 : ℝ)..(b - a), φ (Draft.dfgwShift a η t)) := by
  filter_upwards [hX.additive 0 a b ha hab, hX.covariant 0 (b - a) a (sub_nonneg.mpr hab),
    hint] with η hadd hcov hη
  have hshift : (∫ t in (0 : ℝ)..(b - a), φ (Draft.dfgwShift a η t)) =
      ∫ t in a..b, φ (η t) := by
    change (∫ t in (0 : ℝ)..(b - a), φ (η (t + a))) = _
    simpa only [zero_add, sub_add_cancel] using
      (intervalIntegral.integral_comp_add_right (fun t => φ (η t)) (a := 0) (b := b - a) a)
  have hsum := intervalIntegral.integral_add_adjacent_intervals hη.1 hη.2
  simp only [zero_add, sub_add_cancel] at hcov
  rw [hshift]
  change (X 0 b η - ∫ t in (0 : ℝ)..b, φ (η t)) -
      (X 0 a η - ∫ t in (0 : ℝ)..a, φ (η t)) =
      X 0 (b - a) (Draft.dfgwShift a η) - ∫ t in a..b, φ (η t)
  rw [hcov]
  rw [← hadd, ← hsum]
  abel

end EinsteinFull.External.DFGW
