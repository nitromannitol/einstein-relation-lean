import EinsteinRelation.Diffusion.ClockInverseSupport

open Filter MeasureTheory
open scoped NNReal Topology

namespace EinsteinRelation.Clock.PhysicalClockSpeedMeaningV5

open EinsteinRelation.Clock.InverseMeaningV3

/-- The clock rate of a reduced path in its original nonnegative time variable. -/
def HasClockSpeed {d : ℕ} (ω : FieldPair d) (γ : Path d) (η : ℝ) : Prop :=
  Tendsto (fun t : ℝ≥0 =>
    (physicalPathClock ω γ t : ℝ) / (t : ℝ)) atTop (𝓝 η)

/-- The inverse-time rate for the same field and path under the actual inverse clock. -/
def HasInverseClockSpeed {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L η : ℝ) (hω : IsRegular L ω) : Prop :=
  Tendsto (fun s : ℝ≥0 =>
    (inversePhysicalPathClock ω γ L hω s : ℝ) / (s : ℝ)) atTop (𝓝 η)

/-- A quenched clock-rate statement over the actual origin path laws of a family. -/
def HasQuenchedClockSpeed {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d) (η : ℝ) : Prop :=
  ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂originLaw (P 0) ω, HasClockSpeed ω γ η

/-- The quenched inverse-rate statement keeps the same physical field and path law. -/
def HasQuenchedInverseClockSpeed {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d) (η : ℝ) : Prop :=
  ∀ᵐ ω ∂Q.measure, ∃ hω : IsRegular Λ₀ ω,
    ∀ᵐ γ ∂originLaw (P 0) ω, HasInverseClockSpeed ω γ Λ₀ η hω

/-- The source clock's positive density lower bound forces a positive limiting speed. -/
theorem hasClockSpeed_pos {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L η : ℝ) (hω : IsRegular L ω) (hη : HasClockSpeed ω γ η) : 0 < η := by
  let c : ℝ := Real.exp (-2 * L)
  have hc : 0 < c := Real.exp_pos _
  have hratio : ∀ᶠ t : ℝ≥0 in atTop,
      c ≤ (physicalPathClock ω γ t : ℝ) / (t : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    exact (le_div_iff₀ htR).2 (physicalPathClock_bounds ω γ L hω.2.1 t).1
  have hcη : c ≤ η := le_of_tendsto_of_tendsto tendsto_const_nhds hη hratio
  exact lt_of_lt_of_le hc hcη

/-- Inverting the actual clock exchanges its positive asymptotic rate with its reciprocal. -/
theorem hasClockSpeed_to_hasInverseClockSpeed {d : ℕ} (ω : FieldPair d)
    (γ : Path d) (L η : ℝ) (hω : IsRegular L ω)
    (hη : HasClockSpeed ω γ η) :
    HasInverseClockSpeed ω γ L η⁻¹ hω := by
  let c : ℝ := Real.exp (-2 * L)
  have hc : 0 < c := Real.exp_pos _
  have hηpos : η ≠ 0 := (hasClockSpeed_pos ω γ L η hω hη).ne'
  let invTime : ℝ≥0 → ℝ≥0 := inversePhysicalPathClock ω γ L hω
  have hinvLower (t : ℝ≥0) :
      c * (t : ℝ) ≤ (invTime t : ℝ) := by
    simpa [invTime, c] using (inversePhysicalPathClock_bounds ω γ L hω t).1
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hlin : Tendsto (fun t : ℝ≥0 => c * (t : ℝ)) atTop atTop :=
    hcoe.const_mul_atTop hc
  have hinvReal : Tendsto (fun t : ℝ≥0 => (invTime t : ℝ)) atTop atTop :=
    tendsto_atTop_mono hinvLower hlin
  have hinv : Tendsto invTime atTop atTop := NNReal.tendsto_coe_atTop.mp hinvReal
  have hcomposed : Tendsto (fun s : ℝ≥0 =>
      (physicalPathClock ω γ (invTime s) : ℝ) / (invTime s : ℝ)) atTop (𝓝 η) := by
    exact hη.comp hinv
  have hreciprocal : Tendsto (fun s : ℝ≥0 =>
      (s : ℝ) / (invTime s : ℝ)) atTop (𝓝 η) := by
    apply hcomposed.congr'
    filter_upwards [] with s
    simp [invTime, physicalPathClock_inversePhysicalPathClock]
  have hreciprocalInv := hreciprocal.inv₀ hηpos
  have hEq : ∀ᶠ s : ℝ≥0 in atTop,
      ((s : ℝ) / (invTime s : ℝ))⁻¹ = (invTime s : ℝ) / (s : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with s hs
    have hsR : (0 : ℝ) < (s : ℝ) := by exact_mod_cast hs
    have hinvR : (0 : ℝ) < (invTime s : ℝ) :=
      lt_of_lt_of_le (mul_pos hc hsR) (hinvLower s)
    field_simp
  exact hreciprocalInv.congr' hEq

/-- The inverse clock has positive speed by the same physical density lower bound. -/
theorem hasInverseClockSpeed_pos {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L η : ℝ) (hω : IsRegular L ω) (hη : HasInverseClockSpeed ω γ L η hω) : 0 < η := by
  let c : ℝ := Real.exp (-2 * L)
  have hc : 0 < c := Real.exp_pos _
  have hratio : ∀ᶠ t : ℝ≥0 in atTop,
      c ≤ (inversePhysicalPathClock ω γ L hω t : ℝ) / (t : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    exact (le_div_iff₀ htR).2 (inversePhysicalPathClock_bounds ω γ L hω t).1
  have hcη : c ≤ η := le_of_tendsto_of_tendsto tendsto_const_nhds hη hratio
  exact lt_of_lt_of_le hc hcη

/-- Recover the original clock rate from the rate of its actual inverse. -/
theorem hasInverseClockSpeed_to_hasClockSpeed {d : ℕ} (ω : FieldPair d)
    (γ : Path d) (L η : ℝ) (hω : IsRegular L ω)
    (hη : HasInverseClockSpeed ω γ L η hω) :
    HasClockSpeed ω γ η⁻¹ := by
  let c : ℝ := Real.exp (-2 * L)
  have hc : 0 < c := Real.exp_pos _
  have hηpos : η ≠ 0 := (hasInverseClockSpeed_pos ω γ L η hω hη).ne'
  let clock : ℝ≥0 → ℝ≥0 := physicalPathClock ω γ
  let invTime : ℝ≥0 → ℝ≥0 := inversePhysicalPathClock ω γ L hω
  have hclockLower (t : ℝ≥0) : c * (t : ℝ) ≤ (clock t : ℝ) := by
    simpa [clock, c] using (physicalPathClock_bounds ω γ L hω.2.1 t).1
  have hcoe : Tendsto (fun t : ℝ≥0 => (t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hlin : Tendsto (fun t : ℝ≥0 => c * (t : ℝ)) atTop atTop :=
    hcoe.const_mul_atTop hc
  have hclockReal : Tendsto (fun t : ℝ≥0 => (clock t : ℝ)) atTop atTop :=
    tendsto_atTop_mono hclockLower hlin
  have hclockTop : Tendsto clock atTop atTop :=
    NNReal.tendsto_coe_atTop.mp hclockReal
  have hcomposed : Tendsto (fun t : ℝ≥0 =>
      (invTime (clock t) : ℝ) / (clock t : ℝ)) atTop (𝓝 η) := by
    exact hη.comp hclockTop
  have hreciprocal : Tendsto (fun t : ℝ≥0 =>
      (t : ℝ) / (clock t : ℝ)) atTop (𝓝 η) := by
    apply hcomposed.congr'
    filter_upwards [] with t
    simp [clock, invTime, inversePhysicalPathClock_physicalPathClock]
  have hreciprocalInv := hreciprocal.inv₀ hηpos
  have hEq : ∀ᶠ t : ℝ≥0 in atTop,
      ((t : ℝ) / (clock t : ℝ))⁻¹ = (clock t : ℝ) / (t : ℝ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    have htR : (0 : ℝ) < (t : ℝ) := by exact_mod_cast ht
    have hclockR : (0 : ℝ) < (clock t : ℝ) :=
      lt_of_lt_of_le (mul_pos hc htR) (hclockLower t)
    field_simp
  have hlimit := hreciprocalInv.congr' hEq
  exact hlimit

/-- The clock-rate and inverse-clock-rate predicates are equivalent without an
additional positivity premise; positivity follows from the actual clock bounds. -/
theorem hasClockSpeed_iff_inverse {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L η : ℝ) (hω : IsRegular L ω) :
    HasClockSpeed ω γ η ↔ HasInverseClockSpeed ω γ L η⁻¹ hω := by
  constructor
  · exact hasClockSpeed_to_hasInverseClockSpeed ω γ L η hω
  · intro h
    simpa [inv_inv] using hasInverseClockSpeed_to_hasClockSpeed ω γ L η⁻¹ hω h

/-- The same reciprocal-rate equivalence holds over the actual quenched origin laws. -/
theorem hasQuenchedClockSpeed_iff_inverse {d : ℕ} {Λ₀ r₀ : ℝ}
    (Q : EnvironmentLaw d Λ₀ r₀) (P : DiffusionFamily d) (η : ℝ) :
    HasQuenchedClockSpeed Q P η ↔ HasQuenchedInverseClockSpeed Q P η⁻¹ := by
  constructor
  · intro hRate
    filter_upwards [hRate, Q.regular] with ω hRateω hω
    refine ⟨hω, ?_⟩
    filter_upwards [hRateω] with γ hγ
    exact hasClockSpeed_to_hasInverseClockSpeed ω γ Λ₀ η hω hγ
  · intro hInverse
    filter_upwards [hInverse] with ω hω
    rcases hω with ⟨hRegular, hInverseω⟩
    filter_upwards [hInverseω] with γ hγ
    simpa [inv_inv] using
      hasInverseClockSpeed_to_hasClockSpeed ω γ Λ₀ η⁻¹ hRegular hγ

/-- The inverse path returns to the same reduced path at the source clock time. -/
theorem inverseClockPath_at_clock {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) (t : ℝ≥0) :
    inverseClockPath ω γ L hω (physicalPathClock ω γ t) = γ t :=
  inverseClockPath_atPhysicalClock ω γ L hω t

/-- A concrete nonconstant continuous path for exercising the clock on actual fields. -/
def coordinateRayPath (d : ℕ) (i : Fin d) : Path d :=
  ⟨fun t => (t : ℝ) • unitVector i, by
    first
      | fun_prop
      | exact NNReal.continuous_coe.fun_smul continuous_const⟩

theorem coordinateRayPath_ne_zero_at_one {d : ℕ} (i : Fin d) :
    coordinateRayPath d i 1 ≠ coordinateRayPath d i 0 := by
  intro h
  have hcoord := congrFun h i
  simp [coordinateRayPath, unitVector] at hcoord

theorem coordinateRayPath_clock_identity {d : ℕ} (ω : FieldPair d)
    (L : ℝ) (hω : IsRegular L ω) (i : Fin d) (t : ℝ≥0) :
    inverseClockPath ω (coordinateRayPath d i) L hω
      (physicalPathClock ω (coordinateRayPath d i) t) = coordinateRayPath d i t :=
  inverseClockPath_at_clock ω (coordinateRayPath d i) L hω t

end EinsteinRelation.Clock.PhysicalClockSpeedMeaningV5
