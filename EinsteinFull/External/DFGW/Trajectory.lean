import EinsteinFull.External.Draft.DFGWInvarianceV2

/-! # Stationary reversible trajectory increments

An integrable antisymmetric increment of a reversible process has mean zero.
Stationarity also makes the mean of an increment independent of its time origin.
-/

open MeasureTheory ProbabilityTheory EinsteinRelation
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

omit [MeasurableSpace S] in
/-- A trajectory reflection is measurable. -/
theorem measurable_refl (τ : ℝ) : Measurable (Draft.dfgwRefl (S := S) τ) :=
  (ContinuousMap.continuous_precomp _).measurable

omit [MeasurableSpace S] in
/-- A trajectory time shift is measurable. -/
theorem measurable_shift (τ : ℝ) : Measurable (Draft.dfgwShift (S := S) τ) :=
  (ContinuousMap.continuous_precomp _).measurable

/-- Every integrable antisymmetric increment of a reversible trajectory has mean zero. -/
theorem integral_increment_eq_zero (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) {a b : ℝ} (hab : a ≤ b) :
    ∫ η, X a b η ∂P = 0 := by
  have hm : AEStronglyMeasurable (X a b) (P.map (Draft.dfgwRefl ((a + b) / 2))) := by
    rw [hP.reversible]
    exact (hX.integrable a b hab).aestronglyMeasurable
  have heq : (∫ η, X a b η ∂P) = -(∫ η, X a b η ∂P) := by
    calc
      (∫ η, X a b η ∂P) = ∫ η, X a b η ∂P.map (Draft.dfgwRefl ((a + b) / 2)) := by
        rw [hP.reversible]
      _ = ∫ η, X a b (Draft.dfgwRefl ((a + b) / 2) η) ∂P :=
        integral_map (measurable_refl _).aemeasurable hm
      _ = ∫ η, -X a b η ∂P := integral_congr_ae (hX.antisymmetric a b hab)
      _ = -(∫ η, X a b η ∂P) := integral_neg _
  ext i
  simp only [Pi.zero_apply]
  have hi := congrFun heq i
  simp only [Pi.neg_apply] at hi
  linarith

/-- The mean of an increment is unchanged by translating its time interval. -/
theorem integral_increment_shift (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) {a b : ℝ} (hab : a ≤ b) (τ : ℝ) :
    (∫ η, X (a + τ) (b + τ) η ∂P) = ∫ η, X a b η ∂P := by
  have hm : AEStronglyMeasurable (X a b) (P.map (Draft.dfgwShift τ)) := by
    rw [hP.stationary]
    exact (hX.integrable a b hab).aestronglyMeasurable
  calc
    (∫ η, X (a + τ) (b + τ) η ∂P) = ∫ η, X a b (Draft.dfgwShift τ η) ∂P :=
      (integral_congr_ae (hX.covariant a b τ hab)).symm
    _ = ∫ η, X a b η ∂P.map (Draft.dfgwShift τ) :=
      (integral_map (measurable_shift τ).aemeasurable
        hm).symm
    _ = ∫ η, X a b η ∂P := by rw [hP.stationary]

end EinsteinFull.External.DFGW
