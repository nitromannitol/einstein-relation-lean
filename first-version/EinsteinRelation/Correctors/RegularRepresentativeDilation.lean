import EinsteinRelation.Correctors.SpatialWeakDilation

/-! Source: `paper/main.tex:735-743`. Positive dilation transports local
continuous volume-class representatives. Only preservation of null sets is
needed; no Jacobian computation is required. -/
open MeasureTheory
namespace EinsteinRelation.Correctors
open External.AKM

/-- A local continuous volume-class representative transfers back through
positive spatial dilation. -/
theorem exists_continuousOn_undilated_representative {d : ℕ}
    (u v : Vec d → ℝ) (r R : ℝ) (hr : 0 < r) (_hR : 0 < R)
    (hv : ContinuousOn v (ball 0 R))
    (heq : (fun x => u (r • x)) =ᵐ[volume.restrict (ball 0 R)] v) :
    ∃ w : Vec d → ℝ, ContinuousOn w (ball 0 (r * R)) ∧
      u =ᵐ[volume.restrict (ball 0 (r * R))] w := by
  have hm : Set.MapsTo (fun x : Vec d => r⁻¹ • x) (ball 0 (r * R)) (ball 0 R) := by
    intro x hx
    have hxn : euclideanNorm x < r * R := by simpa only [ball, sub_zero] using hx
    change euclideanNorm (r⁻¹ • x - 0) < R
    rw [sub_zero, Environment.AKMTestIntegralSupport.euclideanNorm_smul _ (inv_pos.mpr hr).le]
    calc r⁻¹ * euclideanNorm x < r⁻¹ * (r * R) := mul_lt_mul_of_pos_left hxn (inv_pos.mpr hr)
      _ = R := by rw [← mul_assoc, inv_mul_cancel₀ hr.ne', one_mul]
  refine ⟨fun x => v (r⁻¹ • x),
    hv.comp (continuous_const.smul continuous_id).continuousOn hm, ?_⟩
  have hball (S : ℝ) : MeasurableSet (ball (0 : Vec d) S) := by
    unfold ball euclideanNorm euclideanSq dot
    exact (isOpen_lt (by fun_prop) continuous_const).measurableSet
  have ha := (Measure.quasiMeasurePreserving_smul (volume : Measure (Vec d))
    (inv_ne_zero hr.ne')).ae ((ae_restrict_iff' (hball R)).mp heq)
  filter_upwards [ae_restrict_of_ae ha, ae_restrict_mem (hball (r * R))] with x hx hxball
  simpa only [smul_smul, mul_inv_cancel₀ hr.ne', one_smul] using hx (hm hxball)

end EinsteinRelation.Correctors
