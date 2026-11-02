import EinsteinRelation.Clock.PhysicalClock
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Hom.Set
import Mathlib.Topology.Order.MonotoneContinuity

open Filter MeasureTheory
open scoped NNReal Topology

namespace EinsteinRelation.Clock.InverseMeaningV3

/-- The existing physical clock unfolds to the manuscript's exponential density integral. -/
theorem coe_physicalPathClock_explicit {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (t : ℝ≥0) :
    (physicalPathClock ω γ t : ℝ) =
      ∫ u in (0 : ℝ)..(t : ℝ), Real.exp (-2 * ω.2 (γ u.toNNReal)) := rfl

/-- Bounded physical potential gives pointwise lower and upper bounds on the actual clock. -/
theorem physicalPathClock_bounds {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hV : ∀ x, |ω.2 x| ≤ L) (t : ℝ≥0) :
    Real.exp (-2 * L) * (t : ℝ) ≤ (physicalPathClock ω γ t : ℝ) ∧
      (physicalPathClock ω γ t : ℝ) ≤ Real.exp (2 * L) * (t : ℝ) := by
  rw [coe_physicalPathClock]
  exact EinsteinRelation.Clock.pathClock_bounds (clockDensity ω) (reduce ω).2.continuous
    (Real.exp (-2 * L)) (Real.exp (2 * L))
    (fun x => clockDensity_bounds ω x L (hV x)) γ t

/-- The physical clock is continuous in nonnegative time. -/
theorem physicalPathClock_continuous {d : ℕ} (ω : FieldPair d) (γ : Path d) :
    Continuous (physicalPathClock ω γ) := by
  let f : ℝ → ℝ := fun u => clockDensity ω (γ u.toNNReal)
  have hf : Continuous f := by
    exact (reduce ω).2.continuous.comp (γ.continuous.comp continuous_real_toNNReal)
  have hfi : ∀ a b, IntervalIntegrable f volume a b := fun a b => hf.intervalIntegrable a b
  have hprim := (intervalIntegral.continuous_primitive hfi 0).comp NNReal.continuous_coe
  have hreal : Continuous (fun t : ℝ≥0 => pathClock (clockDensity ω) γ t) := hprim
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
    have hadj :=
      intervalIntegral.integral_add_adjacent_intervals (hfi 0 (s : ℝ)) (hfi (s : ℝ) (t : ℝ))
    exact hadj
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
      have h1 : ∫ _ in (s : ℝ)..(t : ℝ), Real.exp (-2 * L) ≤ ∫ u in (s : ℝ)..(t : ℝ), f u := hinc
      rw [intervalIntegral.integral_const, smul_eq_mul,
        mul_comm ((t : ℝ) - (s : ℝ)) (Real.exp (-2 * L))] at h1
      exact h1
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
    rw [coe_physicalPathClock, NNReal.coe_zero]
    simp [pathClock]
  have hrange := intermediate_value_Icc (show (0 : ℝ≥0) ≤ t from zero_le)
      (physicalPathClock_continuous ω γ).continuousOn
  have hy : y ∈ Set.Icc (physicalPathClock ω γ 0) (physicalPathClock ω γ t) := by
    rw [hzero]
    exact ⟨zero_le, ht t le_rfl⟩
  obtain ⟨s, _, hs⟩ := hrange hy
  exact ⟨s, hs⟩

/-- The actual physical clock as an order isomorphism, using only regular-field bounds. -/
noncomputable def physicalPathClockOrderIso {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) : ℝ≥0 ≃o ℝ≥0 :=
  StrictMono.orderIsoOfSurjective (physicalPathClock ω γ)
    (physicalPathClock_strictMono ω γ L hω)
    (physicalPathClock_surjective ω γ L hω)

@[simp] theorem physicalPathClockOrderIso_apply {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) (t : ℝ≥0) :
    physicalPathClockOrderIso ω γ L hω t = physicalPathClock ω γ t := by
  rfl

/-- Inverse clock, with the exact two inverse identities inherited from the order isomorphism. -/
noncomputable def inversePhysicalPathClock {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) (t : ℝ≥0) : ℝ≥0 :=
  (physicalPathClockOrderIso ω γ L hω).symm t

@[simp] theorem inversePhysicalPathClock_physicalPathClock {d : ℕ} (ω : FieldPair d)
    (γ : Path d) (L : ℝ) (hω : IsRegular L ω) (t : ℝ≥0) :
    inversePhysicalPathClock ω γ L hω (physicalPathClock ω γ t) = t := by
  exact (physicalPathClockOrderIso ω γ L hω).symm_apply_apply t

@[simp] theorem physicalPathClock_inversePhysicalPathClock {d : ℕ} (ω : FieldPair d)
    (γ : Path d) (L : ℝ) (hω : IsRegular L ω) (t : ℝ≥0) :
    physicalPathClock ω γ (inversePhysicalPathClock ω γ L hω t) = t := by
  exact (physicalPathClockOrderIso ω γ L hω).apply_symm_apply t

/-- The inverse time has the bounds obtained by inverting the clock bounds. -/
theorem inversePhysicalPathClock_bounds {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) (t : ℝ≥0) :
    Real.exp (-2 * L) * (t : ℝ) ≤
        (inversePhysicalPathClock ω γ L hω t : ℝ) ∧
      (inversePhysicalPathClock ω γ L hω t : ℝ) ≤
        Real.exp (2 * L) * (t : ℝ) := by
  let c : ℝ := Real.exp (-2 * L)
  let C : ℝ := Real.exp (2 * L)
  have hc : 0 < c := Real.exp_pos _
  have hC : 0 < C := Real.exp_pos _
  have hfactor : c * C = 1 := by
    dsimp [c, C]
    rw [← Real.exp_add]
    rw [show (-2 * L) + (2 * L) = 0 by ring, Real.exp_zero]
  have hb := physicalPathClock_bounds ω γ L hω.2.1
    (inversePhysicalPathClock ω γ L hω t)
  have hclock :
      (physicalPathClock ω γ (inversePhysicalPathClock ω γ L hω t) : ℝ) =
        (t : ℝ) := congrArg ((↑) : ℝ≥0 → ℝ)
          (physicalPathClock_inversePhysicalPathClock ω γ L hω t)
  rw [hclock] at hb
  constructor
  · calc
      c * (t : ℝ) ≤ c * (C * (inversePhysicalPathClock ω γ L hω t : ℝ)) :=
        mul_le_mul_of_nonneg_left hb.2 hc.le
      _ = (c * C) * (inversePhysicalPathClock ω γ L hω t : ℝ) := by ring
      _ = (inversePhysicalPathClock ω γ L hω t : ℝ) := by rw [hfactor]; simp
  · calc
      (inversePhysicalPathClock ω γ L hω t : ℝ) =
          (c * C) * (inversePhysicalPathClock ω γ L hω t : ℝ) := by
        rw [hfactor]; ring
      _ = C * (c * (inversePhysicalPathClock ω γ L hω t : ℝ)) := by ring
      _ ≤ C * (t : ℝ) := mul_le_mul_of_nonneg_left hb.1 hC.le

/-- The inverse clock is uniquely determined by either inverse equation. -/
theorem inversePhysicalPathClock_unique {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) (t s : ℝ≥0)
    (hs : physicalPathClock ω γ s = t) :
    inversePhysicalPathClock ω γ L hω t = s := by
  apply (physicalPathClockOrderIso ω γ L hω).injective
  simp only [physicalPathClockOrderIso_apply,
    physicalPathClock_inversePhysicalPathClock, hs]

/-- The inverse time does not depend on the regularity bound or its proof. -/
theorem inversePhysicalPathClock_independent {d : ℕ} (ω : FieldPair d) (γ : Path d)
    {L₁ L₂ : ℝ} (hω₁ : IsRegular L₁ ω) (hω₂ : IsRegular L₂ ω) (t : ℝ≥0) :
    inversePhysicalPathClock ω γ L₁ hω₁ t =
      inversePhysicalPathClock ω γ L₂ hω₂ t := by
  apply inversePhysicalPathClock_unique ω γ L₁ hω₁ t
  exact physicalPathClock_inversePhysicalPathClock ω γ L₂ hω₂ t

/-- The inverse clock fixes the origin. -/
theorem inversePhysicalPathClock_zero {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) :
    inversePhysicalPathClock ω γ L hω 0 = 0 := by
  have h := inversePhysicalPathClock_bounds ω γ L hω 0
  apply NNReal.eq
  exact le_antisymm (by simpa using h.2) (by positivity)

/-- The continuous path obtained by evaluating the original path at inverse-clock time. -/
noncomputable def inverseClockPath {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) : Path d :=
  ⟨fun t => γ (inversePhysicalPathClock ω γ L hω t),
    γ.continuous.comp (physicalPathClockOrderIso ω γ L hω).symm.continuous⟩

/-- The source pathwise identity `X(A(t)) = Y(t)` for the constructed inverse path. -/
theorem inverseClockPath_atPhysicalClock {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) (t : ℝ≥0) :
    inverseClockPath ω γ L hω (physicalPathClock ω γ t) = γ t := by
  change γ (inversePhysicalPathClock ω γ L hω
    (physicalPathClock ω γ t)) = γ t
  rw [inversePhysicalPathClock_physicalPathClock]

/-- Time change preserves the initial point of the path. -/
theorem inverseClockPath_zero {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) : inverseClockPath ω γ L hω 0 = γ 0 := by
  change γ (inversePhysicalPathClock ω γ L hω 0) = γ 0
  rw [inversePhysicalPathClock_zero]

/-- A path started at the origin remains started at the origin after time change. -/
theorem inverseClockPath_startsAtOrigin {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) (hγ : γ 0 = 0) :
    inverseClockPath ω γ L hω 0 = 0 := by
  rw [inverseClockPath_zero, hγ]

/-- The reparameterized path is independent of the regularity witness. -/
theorem inverseClockPath_independent {d : ℕ} (ω : FieldPair d) (γ : Path d)
    {L₁ L₂ : ℝ} (hω₁ : IsRegular L₁ ω) (hω₂ : IsRegular L₂ ω) :
    inverseClockPath ω γ L₁ hω₁ = inverseClockPath ω γ L₂ hω₂ := by
  apply ContinuousMap.ext
  intro t
  exact congrArg γ (inversePhysicalPathClock_independent ω γ hω₁ hω₂ t)

end EinsteinRelation.Clock.InverseMeaningV3
