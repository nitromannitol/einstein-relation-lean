import EinsteinRelation.Diffusion.VelocityTimeChange

/-!
# Velocity under an inverse clock

A reduced path with a velocity transfers that velocity through an asymptotically linear,
increasing clock. The identity is the pathwise time-change step used in the velocity law of
Gantert–Mathieu–Piatnitski, Sections 2.3 and 3.
-/

open Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.Regeneration

/-- If a clock has positive asymptotic rate, reparameterizing a path by its inverse gives
velocity equal to the original velocity divided by the clock rate. -/
theorem hasPathVelocity_comp_inverse_clock {d : ℕ} (γ : Path d)
    (A : ℝ≥0 ≃o ℝ≥0) (v : Vec d) (η : ℝ) (hη : 0 < η)
    (hclock : Tendsto (fun t : ℝ≥0 => (A t : ℝ) / t) atTop (𝓝 η))
    (hvel : HasPathVelocity γ v) :
    Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • γ (A.symm t)) atTop (𝓝 (η⁻¹ • v)) := by
  have hB : Tendsto A.symm atTop atTop := A.symm.tendsto_atTop
  have hrate : Tendsto (fun t : ℝ≥0 => (t : ℝ) / (A.symm t : ℝ)) atTop (𝓝 η) := by
    apply (hclock.comp hB).congr'
    filter_upwards with t
    change (A (A.symm t) : ℝ) / (A.symm t : ℝ) = (t : ℝ) / (A.symm t : ℝ)
    rw [A.apply_symm_apply]
  have hinv : Tendsto (fun t : ℝ≥0 => (A.symm t : ℝ) / (t : ℝ)) atTop (𝓝 η⁻¹) := by
    simpa only [inv_div] using hrate.inv₀ hη.ne'
  have hv : Tendsto (fun t : ℝ≥0 => (A.symm t : ℝ)⁻¹ • γ (A.symm t)) atTop (𝓝 v) :=
    hvel.comp hB
  have h := hinv.smul hv
  apply h.congr'
  filter_upwards [hB.eventually (eventually_gt_atTop 0)] with t ht
  have ht' : (A.symm t : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ht)
  rw [smul_smul]
  congr 1
  field_simp

/-- The inverse physical-clock path has the reduced velocity divided by the physical-clock
rate whenever that rate exists and is positive. -/
theorem inversePhysicalClock_hasPathVelocity {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) (v : Vec d) (η : ℝ) (hη : 0 < η)
    (hclock : Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t)
      atTop (𝓝 η)) (hvel : HasPathVelocity γ v) :
    HasPathVelocity (Clock.InverseMeaningV3.inverseClockPath ω γ L hω) (η⁻¹ • v) := by
  exact hasPathVelocity_comp_inverse_clock γ
    (Clock.InverseMeaningV3.physicalPathClockOrderIso ω γ L hω) v η hη hclock hvel

end EinsteinFull.Regeneration
