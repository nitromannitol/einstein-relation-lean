import Mathlib.MeasureTheory.Integral.DominatedConvergence
import EinsteinRelationAudit.SharpExample.Vocabulary.Clock.PhysicalClock

/-! Restated from the library module `EinsteinRelation.Diffusion.ClockInverseSupport`:
the declarations of that module that the statement of
`EinsteinRelationAudit.SharpExample.mobility_rate_sharp` depends on, in their module context. -/

open Filter MeasureTheory
open scoped NNReal Topology
namespace EinsteinRelation.Clock.InverseMeaningV3
/-- The physical clock is continuous in nonnegative time. -/
theorem physicalPathClock_continuous {d : ℕ} (ω : FieldPair d) (γ : Path d) :
    Continuous (physicalPathClock ω γ) := by
  let f : ℝ → ℝ := fun u => clockDensity ω (γ u.toNNReal)
  have hf : Continuous f := by
    exact (reduce ω).2.continuous.comp (γ.continuous.comp continuous_real_toNNReal)
  have hfi : ∀ a b, IntervalIntegrable f volume a b := fun a b => hf.intervalIntegrable a b
  have hreal : Continuous (fun t : ℝ≥0 => pathClock (clockDensity ω) γ t) := by
    simpa [pathClock, f] using (intervalIntegral.continuous_primitive hfi 0).comp NNReal.continuous_coe
  change Continuous (fun t : ℝ≥0 =>
    (⟨pathClock (clockDensity ω) γ t,
      intervalIntegral.integral_nonneg t.property
        (fun u _ => (clockDensity_pos ω (γ u.toNNReal)).le)⟩ : ℝ≥0))
  exact hreal.subtype_mk fun t => by
    exact intervalIntegral.integral_nonneg t.property
      (fun u _ => (clockDensity_pos ω (γ u.toNNReal)).le)
/-- The physical clock is strictly increasing, by the pointwise positive lower density bound. -/
theorem physicalPathClock_strictMono {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) : StrictMono (physicalPathClock ω γ) := by
  rcases hω with ⟨_, hV, _, _⟩
  let f : ℝ → ℝ := fun u => clockDensity ω (γ u.toNNReal)
  have hf : Continuous f := by
    exact (reduce ω).2.continuous.comp (γ.continuous.comp continuous_real_toNNReal)
  have hfi : ∀ a b, IntervalIntegrable f volume a b := fun a b => hf.intervalIntegrable a b
  intro s t hst
  have hsplit : pathClock (clockDensity ω) γ s +
      (∫ u in (s : ℝ)..(t : ℝ), f u) = pathClock (clockDensity ω) γ t := by
    simpa [pathClock, f] using
      (intervalIntegral.integral_add_adjacent_intervals (hfi 0 (s : ℝ)) (hfi (s : ℝ) (t : ℝ)))
  have hlo := Real.exp_pos (-2 * L)
  have hinc := intervalIntegral.integral_mono_on
    (show (s : ℝ) ≤ (t : ℝ) by exact_mod_cast hst.le)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => Real.exp (-2 * L)) volume
      (s : ℝ) (t : ℝ))
    (hfi (s : ℝ) (t : ℝ))
    (fun u _ => (clockDensity_bounds ω (γ u.toNNReal) L (hV (γ u.toNNReal))).1)
  have hgap : 0 < Real.exp (-2 * L) * ((t : ℝ) - (s : ℝ)) := by
    exact mul_pos hlo (sub_pos.mpr (by exact_mod_cast hst))
  have hpositive : 0 < ∫ u in (s : ℝ)..(t : ℝ), f u := by
    have hinc' : Real.exp (-2 * L) * ((t : ℝ) - (s : ℝ)) ≤
        ∫ u in (s : ℝ)..(t : ℝ), f u := by
      simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hinc
    exact lt_of_lt_of_le hgap hinc'
  change (physicalPathClock ω γ s : ℝ) < (physicalPathClock ω γ t : ℝ)
  rw [coe_physicalPathClock, coe_physicalPathClock]
  rw [show pathClock (clockDensity ω) γ s =
      pathClock (clockDensity ω) γ t - ∫ u in (s : ℝ)..(t : ℝ), f u by linarith]
  linarith
/-- The physical clock maps nonnegative time onto nonnegative time. -/
theorem physicalPathClock_surjective {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) : Function.Surjective (physicalPathClock ω γ) := by
  rcases hω with ⟨_, hV, _, _⟩
  intro y
  have htop : Tendsto (physicalPathClock ω γ) atTop atTop :=
    physicalPathClock_tendsto_atTop ω γ L hV
  have hev : ∀ᶠ t in atTop, y ≤ physicalPathClock ω γ t := tendsto_atTop.1 htop y
  obtain ⟨t, ht⟩ := Filter.eventually_atTop.1 hev
  have hzero : physicalPathClock ω γ 0 = 0 := by
    apply NNReal.eq
    simp [physicalPathClock, pathClock]
  have hrange := intermediate_value_Icc (show (0 : ℝ≥0) ≤ t from zero_le t)
      (physicalPathClock_continuous ω γ).continuousOn
  have hy : y ∈ Set.Icc (physicalPathClock ω γ 0) (physicalPathClock ω γ t) := by
    rw [hzero]
    exact ⟨zero_le y, ht t le_rfl⟩
  obtain ⟨s, _, hs⟩ := hrange hy
  exact ⟨s, hs⟩
/-- The actual physical clock as an order isomorphism, using only regular-field bounds. -/
noncomputable def physicalPathClockOrderIso {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (physicalPathClock ω γ)
    (physicalPathClock_strictMono ω γ L hω)
    (physicalPathClock_surjective ω γ L hω)
/-- Inverse clock, with the exact two inverse identities inherited from the order isomorphism. -/
noncomputable def inversePhysicalPathClock {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) (t : ℝ≥0) : ℝ≥0 :=
  (physicalPathClockOrderIso ω γ L hω).symm t
/-- The continuous path obtained by evaluating the original path at inverse-clock time. -/
noncomputable def inverseClockPath {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) : Path d :=
  ⟨fun t => γ (inversePhysicalPathClock ω γ L hω t),
    γ.continuous.comp (physicalPathClockOrderIso ω γ L hω).symm.continuous⟩
end EinsteinRelation.Clock.InverseMeaningV3
