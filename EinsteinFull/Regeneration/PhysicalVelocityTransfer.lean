import EinsteinFull.Regeneration.CoordinateVelocity
import EinsteinFull.Regeneration.InverseClockVelocity

/-!
# Transfer of reduced velocity to the physical diffusion

The inverse physical clock transfers a reduced quenched velocity to the physical law when
its asymptotic rate and the physical-law identification are known. These two source-specific
facts remain explicit hypotheses.
-/

open MeasureTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.Regeneration

/-- Vector-valued path velocity convergence is a measurable path event. -/
theorem measurableSet_path_velocity {d : ℕ} (v : Vec d) :
    MeasurableSet {γ : Path d | HasPathVelocity γ v} := by
  have heq : {γ : Path d | HasPathVelocity γ v} =
      ⋂ i : Fin d, {γ : Path d | Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ * γ t i) atTop (𝓝 (v i))} := by
    ext γ
    simp only [Set.mem_ofPred_eq, Set.mem_iInter, HasPathVelocity, tendsto_pi_nhds,
      Pi.smul_apply, smul_eq_mul]
  rw [heq]
  exact MeasurableSet.iInter fun i => measurableSet_coordinate_velocity i (v i)

/-- An identified inverse-clock image has quenched velocity equal to the reduced velocity
divided by the positive physical-clock rate. -/
theorem quenched_velocity_of_inverse_clock {d : ℕ}
    (Q : Measure (FieldPair d))
    (P P' : ProbabilityTheory.Kernel (FieldPair d) (Path d)) (L : ℝ)
    (hreg : ∀ᵐ ω ∂Q, IsRegular L ω)
    (hTC : ∀ᵐ ω ∂Q, ∀ hω : IsRegular L ω,
      P ω = Measure.map (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ L hω) (P' ω))
    (v : Vec d) (η : ℝ) (hη : 0 < η) (hvel : HasQuenchedVelocity Q P' v)
    (hclock : ∀ᵐ ω ∂Q, ∀ᵐ γ ∂P' ω,
      Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop (𝓝 η)) :
    HasQuenchedVelocity Q P (η⁻¹ • v) := by
  filter_upwards [hreg, hTC, hvel, hclock] with ω hω hωTC hωvel hωclock
  rw [hωTC hω]
  have hmeas : AEMeasurable (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ L hω)
      (P' ω) :=
    ((Clock.PathMapV4.measurable_inverseClockPathMap (d := d) (L := L)).comp
      (measurable_const (a := (⟨ω, hω⟩ : Clock.PathMapV4.PhysicalInput d L)).prodMk
        measurable_id)).aemeasurable
  apply (ae_map_iff hmeas (measurableSet_path_velocity (η⁻¹ • v))).mpr
  filter_upwards [hωvel, hωclock] with γ hγvel hγclock
  exact inversePhysicalClock_hasPathVelocity ω γ L hω v η hη hγclock hγvel

/-- A positive force component stays positive under the positive inverse-clock scaling. -/
theorem inverse_clock_velocity_component_pos {d : ℕ} (v : Vec d) (i : Fin d) (η : ℝ)
    (hη : 0 < η) (hv : 0 < v i) : 0 < (η⁻¹ • v) i := by
  simpa only [Pi.smul_apply, smul_eq_mul] using mul_pos (inv_pos.mpr hη) hv

end EinsteinFull.Regeneration
