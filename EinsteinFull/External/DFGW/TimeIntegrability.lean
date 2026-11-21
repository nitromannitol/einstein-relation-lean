import EinsteinFull.External.DFGW.JointIntegrability

/-! # Time integrability along stationary trajectories

An integrable state observable is integrable along almost every trajectory on every fixed
bounded interval, by stationarity of the one-time marginals and Fubini's theorem.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- An integrable state observable is almost surely time-integrable on a fixed interval. -/
theorem ae_intervalIntegrable_observable (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    {d : ℕ} (φ : S → Vec d) (hφ : Integrable φ μ) {a b : ℝ} (hab : a ≤ b) :
    ∀ᵐ η ∂P, IntervalIntegrable (fun t => φ (η t)) volume a b := by
  let : IsProbabilityMeasure P := hP.probability
  have hprod := integrable_joint_observable hP φ hφ a b
  filter_upwards [hprod.prod_left_ae] with η hη
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2 hη

variable {d : ℕ} {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- The compensated process has stationary increments when the state drift is integrable. -/
theorem compensated_increment_eq_shift_of_integrable (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : Integrable φ μ)
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    (fun η => (X 0 b η - ∫ t in (0 : ℝ)..b, φ (η t)) -
      (X 0 a η - ∫ t in (0 : ℝ)..a, φ (η t))) =ᵐ[P]
    (fun η => X 0 (b - a) (Draft.dfgwShift a η) -
      ∫ t in (0 : ℝ)..(b - a), φ (Draft.dfgwShift a η t)) :=
  compensated_increment_eq_shift hX φ ha hab
    ((ae_intervalIntegrable_observable hP φ hφ ha).and
      (ae_intervalIntegrable_observable hP φ hφ hab))

end EinsteinFull.External.DFGW
