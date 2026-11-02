import EinsteinRelation.Correctors.RootIntegralAverage

/-! Source: `paper/main.tex:718-723,727-731`. Local L² membership and
finite restricted Lebesgue measure at arbitrary Euclidean ball centers. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM Environment.AKMTestIntegralSupport TimeChange

/-- Local L² on origin balls gives L² on every ball, without imposing
stationarity or continuity of the function. -/
theorem memLp_on_euclideanBall_of_origin_balls {d : ℕ} {E : Type*}
    [NormedAddCommGroup E] (u : Vec d → E)
    (hu : ∀ R : ℝ, 0 < R → MemLp u 2 (volume.restrict (ball 0 R)))
    (z : Vec d) (R : ℝ) (hR : 0 < R) :
    MemLp u 2 (volume.restrict (ball z R)) := by
  have hsub : ball z R ⊆ ball (0 : Vec d) (R + euclideanNorm z) := by
    intro x hx
    have ht := euclideanNorm_add_le (x - z) z
    rw [sub_add_cancel] at ht
    change euclideanNorm (x - z) < R at hx
    change euclideanNorm (x - 0) < R + euclideanNorm z
    rw [sub_zero]
    linarith
  exact (hu (R + euclideanNorm z)
    (add_pos_of_pos_of_nonneg hR (Real.sqrt_nonneg _))).mono_measure
    (Measure.restrict_mono_set volume hsub)

/-- Every positive Euclidean ball has finite restricted coordinate volume. -/
theorem isFiniteMeasure_restrict_euclideanBall {d : ℕ} (z : Vec d) (R : ℝ)
    (hR : 0 < R) : IsFiniteMeasure (volume.restrict (ball z R)) := by
  have hm : 0 < volume.real (ball z R) := by
    simpa only [measureReal_def, volume_euclideanBall_center] using
      ball_volume_pos_finite d R hR
  exact ⟨by simpa using (ENNReal.toReal_pos_iff.mp hm).2⟩

end EinsteinRelation.Correctors
