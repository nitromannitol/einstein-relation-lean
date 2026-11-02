import EinsteinRelation.Diffusion.JointClockPathMapSupport
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import EinsteinRelation.Clock.ClockExpectation
import EinsteinRelation.Diffusion.ClockInverseSupport
import EinsteinRelation.Probability.PathMaps
import EinsteinRelation.TimeChange.EuclideanTransport
import Mathlib.Dynamics.BirkhoffSum.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecificLimits.FloorPow
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import EinsteinRelation.Clock.ClockSpeedMeaningSupport
import EinsteinFull.Calculus.C12SharpClockReduction
import EinsteinFull.Calculus.C16FoundationInstantiation
import EinsteinFull.Calculus.C11SharpHarmonicEnergy
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeTimeChange

/-! Deterministic cocycle and block-sum identities for the actual physical clock. -/

open EinsteinRelation MeasureTheory Filter
open scoped NNReal ENNReal Topology BigOperators

namespace EinsteinFull.Blueprint

/-- Translate the environment to the current path position and recenter the future path. -/
noncomputable def c12ClockShift {d : ℕ} (s : ℝ≥0)
    (z : FieldPair d × Path d) : FieldPair d × Path d :=
  (translate (z.2 s) z.1,
    ⟨fun t => z.2 (s + t) - z.2 s,
      (z.2.continuous.comp (continuous_const.add continuous_id)).sub continuous_const⟩)

/-- The physical clock accumulated over a unit block, centered by its proposed rate. -/
noncomputable def c12CenteredClockBlock {d : ℕ} (η : ℝ)
    (z : FieldPair d × Path d) : ℝ :=
  (Clock.physicalPathClock z.1 z.2 1 : ℝ) - η

/-- The physical clock is additive under translation and recentering of the actual path. -/
theorem c12_physical_clock_cocycle {d : ℕ} (s t : ℝ≥0)
    (z : FieldPair d × Path d) :
    (Clock.physicalPathClock z.1 z.2 (s + t) : ℝ) =
      (Clock.physicalPathClock z.1 z.2 s : ℝ) +
      (Clock.physicalPathClock (c12ClockShift s z).1 (c12ClockShift s z).2 t : ℝ) := by
  let f : ℝ → ℝ := fun u => clockDensity z.1 (z.2 u.toNNReal)
  have hf : Continuous f := Clock.continuous_clockDensity_along z.1 z.2
  have hshift :
      (∫ u in (0 : ℝ)..(t : ℝ),
        clockDensity (c12ClockShift s z).1 ((c12ClockShift s z).2 u.toNNReal)) =
      ∫ u in (0 : ℝ)..(t : ℝ), f ((s : ℝ) + u) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : 0 ≤ u := ((Set.uIcc_of_le t.property) ▸ hu).1
    have htime : s + u.toNNReal = ((s : ℝ) + u).toNNReal := by
      simpa only [Real.toNNReal_coe] using
        (Real.toNNReal_add (r := (s : ℝ)) (p := u) s.property hu0).symm
    change Real.exp (-2 * z.1.2 (z.2 s + (z.2 (s + u.toNNReal) - z.2 s))) = _
    rw [← add_sub_assoc, add_sub_cancel_left, htime]
    rfl
  change (∫ u in (0 : ℝ)..((s : ℝ) + (t : ℝ)), f u) =
    (∫ u in (0 : ℝ)..(s : ℝ), f u) +
      (∫ u in (0 : ℝ)..(t : ℝ),
        clockDensity (c12ClockShift s z).1 ((c12ClockShift s z).2 u.toNNReal))
  rw [hshift, intervalIntegral.integral_comp_add_left, add_zero]
  exact (intervalIntegral.integral_add_adjacent_intervals
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)).symm

/-- Integer-time centered clocks are the Birkhoff sums of actual unit clock blocks. -/
theorem c12_centered_clock_birkhoff_identity {d : ℕ} (η : ℝ)
    (n : ℕ) (z : FieldPair d × Path d) :
    (Clock.physicalPathClock z.1 z.2 (n : ℝ≥0) : ℝ) - (n : ℝ) * η =
      birkhoffSum (c12ClockShift 1) (c12CenteredClockBlock η) n z := by
  induction n generalizing z with
  | zero =>
      simp only [Nat.cast_zero, Clock.coe_physicalPathClock, Clock.pathClock, NNReal.coe_zero,
        intervalIntegral.integral_same, zero_mul, sub_zero, birkhoffSum_zero_apply]
  | succ n ih =>
      rw [birkhoffSum_succ_apply', ← ih (c12ClockShift 1 z)]
      rw [show ((n + 1 : ℕ) : ℝ≥0) = 1 + (n : ℝ≥0) by simp only [Nat.cast_add,
        Nat.cast_one, add_comm]]
      rw [c12_physical_clock_cocycle]
      dsimp only [c12CenteredClockBlock]
      push_cast
      ring

/-- The actual environment-path shift is continuous in the compact-open topologies. -/
theorem continuous_c12ClockShift {d : ℕ} (s : ℝ≥0) :
    Continuous (c12ClockShift (d := d) s) := by
  have hpos : Continuous (fun z : FieldPair d × Path d => z.2 s) :=
    continuous_snd.eval continuous_const
  have htime : Continuous (fun z : FieldPair d × Path d =>
      (⟨fun t => z.2 (s + t),
        z.2.continuous.comp (continuous_const.add continuous_id)⟩ : Path d)) :=
    Probability.continuous_path_time_shift.comp (continuous_const.prodMk continuous_snd)
  exact (Probability.continuous_translate.comp (hpos.prodMk continuous_fst)).prodMk
    (Probability.continuous_path_recenter.comp (hpos.prodMk htime))

/-- Centering a fixed unit clock block preserves continuity. -/
theorem continuous_c12CenteredClockBlock {d : ℕ} (η : ℝ) :
    Continuous (c12CenteredClockBlock (d := d) η) :=
  (Clock.continuous_physicalPathClock_at 1).sub continuous_const

/-- Successive environment-path shifts add their elapsed times. -/
theorem c12ClockShift_add {d : ℕ} (s t : ℝ≥0) (z : FieldPair d × Path d) :
    c12ClockShift t (c12ClockShift s z) = c12ClockShift (s + t) z := by
  apply Prod.ext
  · change translate (z.2 (s + t) - z.2 s) (translate (z.2 s) z.1) =
      translate (z.2 (s + t)) z.1
    rw [translate_add, sub_add_cancel]
  · apply ContinuousMap.ext
    intro u
    change (z.2 (s + (t + u)) - z.2 s) - (z.2 (s + t) - z.2 s) =
      z.2 ((s + t) + u) - z.2 (s + t)
    rw [add_assoc]
    abel

/-- Every recentered shifted path starts at the origin. -/
theorem c12ClockShift_path_zero {d : ℕ} (s : ℝ≥0) (z : FieldPair d × Path d) :
    (c12ClockShift s z).2 0 = 0 := by
  change z.2 (s + 0) - z.2 s = 0
  rw [add_zero, sub_self]

/-- The zero-time shift fixes pairs whose path starts at the origin. -/
theorem c12ClockShift_zero_of_origin {d : ℕ} (z : FieldPair d × Path d)
    (hz : z.2 0 = 0) : c12ClockShift 0 z = z := by
  apply Prod.ext
  · change translate (z.2 0) z.1 = z.1
    rw [hz, translate_zero]
  · apply ContinuousMap.ext
    intro t
    change z.2 (0 + t) - z.2 0 = z.2 t
    rw [zero_add, hz, sub_zero]

/-- Iterating the unit shift agrees with shifting by integer time on origin paths. -/
theorem c12ClockShift_iterate_of_origin {d : ℕ}
    (n : ℕ) (z : FieldPair d × Path d) (hz : z.2 0 = 0) :
    ((c12ClockShift 1)^[n]) z = c12ClockShift (n : ℝ≥0) z := by
  induction n with
  | zero =>
      simpa only [Function.iterate_zero_apply, Nat.cast_zero] using
        (c12ClockShift_zero_of_origin z hz).symm
  | succ n ih =>
      rw [Function.iterate_succ_apply', ih, c12ClockShift_add, Nat.cast_succ]

/-- Centered unit-block averages equal the actual normalized physical-clock error. -/
theorem c12_actual_centered_clock_average {d : ℕ} (η : ℝ)
    (n : ℕ) (z : FieldPair d × Path d) :
    (((n : ℝ) + 1)⁻¹ * ∑ k ∈ Finset.range (n + 1),
      c12CenteredClockBlock η (((c12ClockShift 1)^[k]) z)) =
      (Clock.physicalPathClock z.1 z.2 ((n + 1 : ℕ) : ℝ≥0) : ℝ) /
        ((n : ℝ) + 1) - η := by
  change ((n : ℝ) + 1)⁻¹ *
    birkhoffSum (c12ClockShift 1) (c12CenteredClockBlock η) (n + 1) z = _
  rw [← c12_centered_clock_birkhoff_identity]
  simp only [Nat.cast_add, Nat.cast_one]
  have hn : (n : ℝ) + 1 ≠ 0 := by positivity
  field_simp [hn]

/-- Ratios of the actual physical clock at adjacent real and integer times are close. -/
theorem c12_clock_ratio_integer_comparison {d : ℕ}
    (ω : FieldPair d) (γ : Path d) (L : ℝ)
    (hV : ∀ x : Vec d, |ω.2 x| ≤ L)
    (n : ℕ) (hn : 1 ≤ n) (t : ℝ≥0)
    (hlo : (n : ℝ≥0) ≤ t) (hhi : t ≤ ((n + 1 : ℕ) : ℝ≥0)) :
    |(Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ) -
      (Clock.physicalPathClock ω γ (n : ℝ≥0) : ℝ) / (n : ℝ)| ≤
      2 * Real.exp (2 * L) / (n : ℝ) := by
  have hnpos : 0 < (n : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hn)
  have hnt : (n : ℝ) ≤ (t : ℝ) := by exact_mod_cast hlo
  have htpos : 0 < (t : ℝ) := hnpos.trans_le hnt
  have hgap : (t : ℝ) - (n : ℝ) ≤ 1 := by
    have hhi' : (t : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hhi
    linarith only [hhi']
  have hK : 0 ≤ Real.exp (2 * L) := (Real.exp_pos _).le
  have hclock := Clock.physicalPathClock_le_of_clock_bound ω γ
    (fun s => (clockDensity_bounds ω (pathPosition s γ) L (hV _)).2)
    (n : ℝ≥0)
  rw [NNReal.coe_natCast] at hclock
  have hmono := Clock.physicalPathClock_mono (ω, γ) hlo
  have hinc : (Clock.physicalPathClock ω γ t : ℝ) -
      (Clock.physicalPathClock ω γ (n : ℝ≥0) : ℝ) ≤ Real.exp (2 * L) := by
    let z := c12ClockShift (n : ℝ≥0) (ω, γ)
    have hshiftV : ∀ x : Vec d, |z.1.2 x| ≤ L := fun x => hV (γ n + x)
    have hb := Clock.physicalPathClock_le_of_clock_bound z.1 z.2
      (fun s => (clockDensity_bounds z.1 (pathPosition s z.2) L (hshiftV _)).2)
      (t - (n : ℝ≥0))
    have hc := c12_physical_clock_cocycle (n : ℝ≥0) (t - (n : ℝ≥0)) (ω, γ)
    rw [add_tsub_cancel_of_le hlo] at hc
    rw [NNReal.coe_sub hlo, NNReal.coe_natCast] at hb
    have hsmall := mul_le_mul_of_nonneg_left hgap hK
    change (Clock.physicalPathClock ω γ t : ℝ) =
      (Clock.physicalPathClock ω γ (n : ℝ≥0) : ℝ) +
      (Clock.physicalPathClock z.1 z.2 (t - (n : ℝ≥0)) : ℝ) at hc
    linarith only [hc, hb, hsmall]
  have hnonneg : 0 ≤ (Clock.physicalPathClock ω γ (n : ℝ≥0) : ℝ) :=
    NNReal.coe_nonneg _
  have hmul := mul_le_mul_of_nonneg_left hinc hnpos.le
  have hden := mul_nonneg hnonneg (sub_nonneg.mpr hnt)
  have hmul0 := mul_nonneg hnpos.le (sub_nonneg.mpr hmono)
  have hclockgap := mul_le_mul_of_nonneg_right hclock (sub_nonneg.mpr hnt)
  have hunit := mul_le_mul_of_nonneg_left hgap (mul_nonneg hK hnpos.le)
  have htime := mul_le_mul_of_nonneg_left hnt hK
  have hKt := mul_nonneg hK htpos.le
  have hnum : |(n : ℝ) * (Clock.physicalPathClock ω γ t : ℝ) -
      (t : ℝ) * (Clock.physicalPathClock ω γ (n : ℝ≥0) : ℝ)| ≤
      2 * Real.exp (2 * L) * (t : ℝ) := by
    apply abs_le.mpr
    constructor
    · nlinarith only [hmul0, hclockgap, hunit, htime, hKt]
    · nlinarith only [hmul, hden, htime, hKt]
  have hratio : (Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ) -
      (Clock.physicalPathClock ω γ (n : ℝ≥0) : ℝ) / (n : ℝ) =
      ((n : ℝ) * (Clock.physicalPathClock ω γ t : ℝ) -
        (t : ℝ) * (Clock.physicalPathClock ω γ (n : ℝ≥0) : ℝ)) /
        ((n : ℝ) * (t : ℝ)) := by
    field_simp [ne_of_gt hnpos, ne_of_gt htpos]
  rw [hratio, abs_div, abs_of_pos (mul_pos hnpos htpos)]
  calc
    _ ≤ (2 * Real.exp (2 * L) * (t : ℝ)) / ((n : ℝ) * (t : ℝ)) :=
      div_le_div_of_nonneg_right hnum (mul_nonneg hnpos.le htpos.le)
    _ = 2 * Real.exp (2 * L) / (n : ℝ) := by
      field_simp [ne_of_gt hnpos, ne_of_gt htpos]

/-- A linear error bound for the actual clock transfers to its actual inverse. -/
theorem c12_inverse_clock_error_of_linear_error {d : ℕ}
    (ω : FieldPair d) (γ : Path d) (L : ℝ) (hω : IsRegular L ω)
    (η ε C : ℝ) (hη : 0 < η) (hε : 0 ≤ ε) (hC : 0 ≤ C)
    (herr : ∀ t : ℝ≥0,
      |(Clock.physicalPathClock ω γ t : ℝ) - η * (t : ℝ)| ≤ C + ε * (t : ℝ))
    (s : ℝ≥0) (hs : 0 < s) :
    |(Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s : ℝ) / (s : ℝ) -
      η⁻¹| ≤ C / (η * (s : ℝ)) + ε * Real.exp (2 * L) / η := by
  let τ := Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hs
  have hden : 0 < η * (s : ℝ) := mul_pos hη hspos
  have herrτ : |(s : ℝ) - η * (τ : ℝ)| ≤ C + ε * (τ : ℝ) := by
    simpa only [τ, Clock.InverseMeaningV3.physicalPathClock_inversePhysicalPathClock]
      using herr τ
  have hτ : (τ : ℝ) ≤ Real.exp (2 * L) * (s : ℝ) :=
    (Clock.InverseMeaningV3.inversePhysicalPathClock_bounds ω γ L hω s).2
  have hratio : (τ : ℝ) / (s : ℝ) - η⁻¹ =
      -((s : ℝ) - η * (τ : ℝ)) / (η * (s : ℝ)) := by
    field_simp [ne_of_gt hη, ne_of_gt hspos]
    ring
  change |(τ : ℝ) / (s : ℝ) - η⁻¹| ≤ _
  rw [hratio, abs_div, abs_neg, abs_of_pos hden]
  calc
    _ ≤ (C + ε * (τ : ℝ)) / (η * (s : ℝ)) :=
      div_le_div₀ (add_nonneg hC (mul_nonneg hε (NNReal.coe_nonneg τ)))
        herrτ hden le_rfl
    _ ≤ (C + ε * (Real.exp (2 * L) * (s : ℝ))) / (η * (s : ℝ)) :=
      div_le_div_of_nonneg_right
        (add_le_add le_rfl (mul_le_mul_of_nonneg_left hτ hε)) hden.le
    _ = C / (η * (s : ℝ)) + ε * Real.exp (2 * L) / η := by
      field_simp [ne_of_gt hη, ne_of_gt hspos]

/-- A power error bound for the actual clock transfers to its actual inverse. -/
theorem c12_inverse_clock_error_of_power_error {d : ℕ}
    (ω : FieldPair d) (γ : Path d) (L : ℝ) (hω : IsRegular L ω)
    (η α C : ℝ) (hη : 0 < η) (hα : 0 < α) (hα1 : α < 1) (hC : 0 ≤ C)
    (herr : ∀ t : ℝ≥0, |(Clock.physicalPathClock ω γ t : ℝ) - η * (t : ℝ)| ≤
      C * (Real.rpow (t : ℝ) α + 1)) (s : ℝ≥0) (hs : 0 < s) :
    |(Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s : ℝ) / (s : ℝ) -
      η⁻¹| ≤ (C / η) * Real.exp (2 * L * α) * Real.rpow (s : ℝ) (α - 1) +
        C / (η * (s : ℝ)) := by
  have hαrange : α ∈ Set.Ioo (0 : ℝ) 1 := ⟨hα, hα1⟩
  let τ := Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hs
  have hden : 0 < η * (s : ℝ) := mul_pos hη hspos
  have herrτ : |(s : ℝ) - η * (τ : ℝ)| ≤ C * (Real.rpow (τ : ℝ) α + 1) := by
    simpa only [τ, Clock.InverseMeaningV3.physicalPathClock_inversePhysicalPathClock]
      using herr τ
  have hτ : (τ : ℝ) ≤ Real.exp (2 * L) * (s : ℝ) :=
    (Clock.InverseMeaningV3.inversePhysicalPathClock_bounds ω γ L hω s).2
  have hpower : Real.rpow (τ : ℝ) α ≤
      Real.exp (2 * L * α) * Real.rpow (s : ℝ) α := by
    calc
      _ ≤ Real.rpow (Real.exp (2 * L) * (s : ℝ)) α :=
        Real.rpow_le_rpow (NNReal.coe_nonneg τ) hτ hαrange.1.le
      _ = Real.exp (2 * L * α) * Real.rpow (s : ℝ) α := by
        simp only [Real.rpow_eq_pow]
        rw [Real.mul_rpow (Real.exp_pos _).le hspos.le, ← Real.exp_mul]
  have hratio : (τ : ℝ) / (s : ℝ) - η⁻¹ =
      -((s : ℝ) - η * (τ : ℝ)) / (η * (s : ℝ)) := by
    field_simp [ne_of_gt hη, ne_of_gt hspos]
    ring
  change |(τ : ℝ) / (s : ℝ) - η⁻¹| ≤ _
  rw [hratio, abs_div, abs_neg, abs_of_pos hden]
  calc
    _ ≤ (C * (Real.rpow (τ : ℝ) α + 1)) / (η * (s : ℝ)) :=
      div_le_div_of_nonneg_right herrτ hden.le
    _ ≤ (C * (Real.exp (2 * L * α) * Real.rpow (s : ℝ) α + 1)) /
        (η * (s : ℝ)) :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (add_le_add hpower le_rfl) hC) hden.le
    _ = (C / η) * Real.exp (2 * L * α) * Real.rpow (s : ℝ) (α - 1) +
        C / (η * (s : ℝ)) := by
      simp only [Real.rpow_eq_pow]
      rw [Real.rpow_sub_one (ne_of_gt hspos)]
      field_simp [ne_of_gt hη, ne_of_gt hspos]

/-- A positive asymptotic rate for the actual clock gives the reciprocal inverse rate. -/
theorem c12_inverse_clock_ratio_tendsto {d : ℕ}
    (ω : FieldPair d) (γ : Path d) (L : ℝ) (hω : IsRegular L ω)
    (η : ℝ) (hη : 0 < η)
    (hclock : Tendsto (fun t : ℝ≥0 =>
      (Clock.physicalPathClock ω γ t : ℝ) / (t : ℝ)) atTop (𝓝 η)) :
    Tendsto (fun s : ℝ≥0 =>
      (Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s : ℝ) / (s : ℝ))
      atTop (𝓝 η⁻¹) := by
  let τ := Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω
  have hcoe : Tendsto (fun s : ℝ≥0 => (s : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hτreal : Tendsto (fun s => (τ s : ℝ)) atTop atTop :=
    tendsto_atTop_mono
      (fun s => (Clock.InverseMeaningV3.inversePhysicalPathClock_bounds ω γ L hω s).1)
      (hcoe.const_mul_atTop (Real.exp_pos (-2 * L)))
  have hτ : Tendsto τ atTop atTop := NNReal.tendsto_coe_atTop.mp hτreal
  have hreciprocal := (hclock.comp hτ).inv₀ (ne_of_gt hη)
  apply hreciprocal.congr'
  filter_upwards [] with s
  simp only [Function.comp_apply, τ,
    Clock.InverseMeaningV3.physicalPathClock_inversePhysicalPathClock, inv_div]

/-- An inverse clock transfers an asymptotic velocity with the reciprocal rate. -/
theorem c12_inverse_clock_velocity_tendsto {d : ℕ}
    (ω : FieldPair d) (γ : Path d) (L : ℝ) (hω : IsRegular L ω)
    (η : ℝ) (hη : 0 < η) (v : Vec d)
    (hclock : Tendsto (fun t : ℝ≥0 =>
      (Clock.physicalPathClock ω γ t : ℝ)/(t : ℝ)) atTop (𝓝 η))
    (hvelocity : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • γ t) atTop (𝓝 v)) :
    Tendsto (fun s : ℝ≥0 => (s : ℝ)⁻¹ •
      γ (Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s))
      atTop (𝓝 (η⁻¹ • v)) := by
  let τ := Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω
  have hcoe : Tendsto (fun s : ℝ≥0 => (s : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hτreal : Tendsto (fun s => (τ s : ℝ)) atTop atTop :=
    tendsto_atTop_mono
      (fun s => (Clock.InverseMeaningV3.inversePhysicalPathClock_bounds ω γ L hω s).1)
      (hcoe.const_mul_atTop (Real.exp_pos (-2 * L)))
  have hτ : Tendsto τ atTop atTop := NNReal.tendsto_coe_atTop.mp hτreal
  have hlimit := (c12_inverse_clock_ratio_tendsto ω γ L hω η hη hclock).smul
    (hvelocity.comp hτ)
  apply hlimit.congr'
  filter_upwards [hτreal.eventually (eventually_gt_atTop 0)] with s hs
  change ((τ s : ℝ) / (s : ℝ)) • ((τ s : ℝ)⁻¹ • γ (τ s)) =
    (s : ℝ)⁻¹ • γ (τ s)
  rw [smul_smul, div_eq_mul_inv,
    mul_comm (τ s : ℝ) ((s : ℝ)⁻¹), mul_assoc,
    mul_inv_cancel₀ (ne_of_gt hs), mul_one]

/-- Quantitative velocity error transferred through the actual inverse clock. -/
theorem c12_inverse_clock_velocity_error {d : ℕ}
    (ω : FieldPair d) (γ : Path d) (L : ℝ) (hω : IsRegular L ω)
    (η C ε A δ : ℝ) (hη : 0 < η) (hC : 0 ≤ C) (hε : 0 ≤ ε)
    (hδ : 0 ≤ δ) (v : Vec d)
    (hclock : ∀ t : ℝ≥0,
      |(Clock.physicalPathClock ω γ t : ℝ)-η*(t : ℝ)| ≤ C+ε*(t : ℝ))
    (hvelocity : ∀ t : ℝ≥0,
      euclideanNorm (γ t-(t : ℝ) • v) ≤ A+δ*(t : ℝ))
    (s : ℝ≥0) (hs : 0 < s) :
    euclideanNorm ((s : ℝ)⁻¹ •
      γ (Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s)-η⁻¹ • v)
    ≤ A/(s : ℝ)+δ*Real.exp (2*L)+euclideanNorm v*
      (C/(η*(s : ℝ))+ε*Real.exp (2*L)/η) := by
  let τ := Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hs
  have hτ : (τ : ℝ) ≤ Real.exp (2 * L) * (s : ℝ) :=
    (Clock.InverseMeaningV3.inversePhysicalPathClock_bounds ω γ L hω s).2
  have hratio := c12_inverse_clock_error_of_linear_error ω γ L hω η ε C hη hε hC hclock s hs
  have hdecomp : (s : ℝ)⁻¹ • γ τ - η⁻¹ • v =
      (s : ℝ)⁻¹ • (γ τ - (τ : ℝ) • v) +
        ((τ : ℝ) / (s : ℝ) - η⁻¹) • v := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change euclideanNorm ((s : ℝ)⁻¹ • γ τ - η⁻¹ • v) ≤ _
  rw [hdecomp]
  calc
    _ ≤ euclideanNorm ((s : ℝ)⁻¹ • (γ τ - (τ : ℝ) • v)) +
        euclideanNorm (((τ : ℝ) / (s : ℝ) - η⁻¹) • v) :=
      TimeChange.euclideanNorm_add_le _ _
    _ = (s : ℝ)⁻¹ * euclideanNorm (γ τ - (τ : ℝ) • v) +
        |(τ : ℝ) / (s : ℝ) - η⁻¹| * euclideanNorm v := by
      rw [TimeChange.euclideanNorm_smul, TimeChange.euclideanNorm_smul,
        abs_of_pos (inv_pos.mpr hspos)]
    _ ≤ (s : ℝ)⁻¹ * (A + δ * (τ : ℝ)) +
        (C / (η * (s : ℝ)) + ε * Real.exp (2 * L) / η) * euclideanNorm v := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left (hvelocity τ) (inv_nonneg.mpr hspos.le)
      · exact mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg _)
    _ ≤ A/(s : ℝ)+δ*Real.exp (2*L)+euclideanNorm v*
        (C/(η*(s : ℝ))+ε*Real.exp (2*L)/η) := by
      have hb := mul_le_mul_of_nonneg_left hτ hδ
      have hb' := mul_le_mul_of_nonneg_left hb (inv_nonneg.mpr hspos.le)
      field_simp [ne_of_gt hspos] at hb' ⊢
      nlinarith

/-- Polynomial path and clock errors transfer through the actual inverse clock. -/
theorem c12_inverse_clock_velocity_error_of_power_error {d : ℕ}
    (ω : FieldPair d) (γ : Path d) (L : ℝ) (hω : IsRegular L ω)
    (η C A α : ℝ) (hη : 0 < η) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hα : 0 ≤ α) (v : Vec d)
    (hclock : ∀ t : ℝ≥0,
      |(Clock.physicalPathClock ω γ t : ℝ)-η*(t : ℝ)| ≤ C*(1+(t : ℝ))^α)
    (hvelocity : ∀ t : ℝ≥0,
      euclideanNorm (γ t-(t : ℝ) • v) ≤ A*(1+(t : ℝ))^α)
    (s : ℝ≥0) (hs : 0 < s) :
    euclideanNorm ((s : ℝ)⁻¹ •
      γ (Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s)-η⁻¹ • v)
    ≤ (A+euclideanNorm v*C/η)*(1+Real.exp (2*L)*(s : ℝ))^α/(s : ℝ) := by
  let τ := Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s
  have hspos : 0 < (s : ℝ) := by exact_mod_cast hs
  have hτ : (τ : ℝ) ≤ Real.exp (2 * L) * (s : ℝ) :=
    (Clock.InverseMeaningV3.inversePhysicalPathClock_bounds ω γ L hω s).2
  have hpower : (1 + (τ : ℝ)) ^ α ≤ (1 + Real.exp (2 * L) * (s : ℝ)) ^ α :=
    Real.rpow_le_rpow (by positivity) (by linarith) hα
  have herr : |(s : ℝ) - η * (τ : ℝ)| ≤ C * (1 + (τ : ℝ)) ^ α := by
    simpa only [τ, Clock.InverseMeaningV3.physicalPathClock_inversePhysicalPathClock]
      using hclock τ
  have hratio : |(τ : ℝ) / (s : ℝ) - η⁻¹| ≤
      C * (1 + (τ : ℝ)) ^ α / (η * (s : ℝ)) := by
    have heq : (τ : ℝ) / (s : ℝ) - η⁻¹ =
        -((s : ℝ) - η * (τ : ℝ)) / (η * (s : ℝ)) := by
      field_simp [ne_of_gt hη, ne_of_gt hspos]
      ring
    rw [heq, abs_div, abs_neg, abs_of_pos (mul_pos hη hspos)]
    exact div_le_div_of_nonneg_right herr (mul_pos hη hspos).le
  have hdecomp : (s : ℝ)⁻¹ • γ τ - η⁻¹ • v =
      (s : ℝ)⁻¹ • (γ τ - (τ : ℝ) • v) +
        ((τ : ℝ) / (s : ℝ) - η⁻¹) • v := by
    ext i
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  change euclideanNorm ((s : ℝ)⁻¹ • γ τ - η⁻¹ • v) ≤ _
  rw [hdecomp]
  calc
    _ ≤ euclideanNorm ((s : ℝ)⁻¹ • (γ τ - (τ : ℝ) • v)) +
        euclideanNorm (((τ : ℝ) / (s : ℝ) - η⁻¹) • v) :=
      TimeChange.euclideanNorm_add_le _ _
    _ = (s : ℝ)⁻¹ * euclideanNorm (γ τ - (τ : ℝ) • v) +
        |(τ : ℝ) / (s : ℝ) - η⁻¹| * euclideanNorm v := by
      rw [TimeChange.euclideanNorm_smul, TimeChange.euclideanNorm_smul,
        abs_of_pos (inv_pos.mpr hspos)]
    _ ≤ (s : ℝ)⁻¹ * (A * (1 + (τ : ℝ)) ^ α) +
        (C * (1 + (τ : ℝ)) ^ α / (η * (s : ℝ))) * euclideanNorm v := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (hvelocity τ) (inv_nonneg.mpr hspos.le))
        (mul_le_mul_of_nonneg_right hratio (Real.sqrt_nonneg _))
    _ ≤ (A + euclideanNorm v * C / η) *
        (1 + Real.exp (2 * L) * (s : ℝ)) ^ α / (s : ℝ) := by
      have ha := mul_le_mul_of_nonneg_left hpower hA
      have hc := mul_le_mul_of_nonneg_left hpower hC
      have hv := Real.sqrt_nonneg (euclideanSq v)
      have h1 := mul_le_mul_of_nonneg_left ha (inv_nonneg.mpr hspos.le)
      have h2 := mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hc (mul_pos hη hspos).le) hv
      calc
        _ ≤ (s : ℝ)⁻¹ * (A * (1 + Real.exp (2 * L) * (s : ℝ)) ^ α) +
            (C * (1 + Real.exp (2 * L) * (s : ℝ)) ^ α /
              (η * (s : ℝ))) * euclideanNorm v := add_le_add h1 h2
        _ = _ := by
          field_simp [ne_of_gt hη, ne_of_gt hspos]


/-- Explicit power rate for velocity under the actual inverse clock. -/
theorem c12_inverse_clock_velocity_power_rate {d : ℕ}
    (ω : FieldPair d) (γ : Path d) (L : ℝ) (hω : IsRegular L ω)
    (η C A α : ℝ) (hη : 0 < η) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hα : 0 ≤ α) (v : Vec d)
    (hclock : ∀ t : ℝ≥0,
      |(Clock.physicalPathClock ω γ t : ℝ)-η*(t : ℝ)| ≤ C*(1+(t : ℝ))^α)
    (hvelocity : ∀ t : ℝ≥0,
      euclideanNorm (γ t-(t : ℝ) • v) ≤ A*(1+(t : ℝ))^α)
    (s : ℝ≥0) (hs : 1 ≤ (s : ℝ)) :
    euclideanNorm ((s : ℝ)⁻¹ •
      γ (Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s)-η⁻¹ • v)
    ≤ (A+euclideanNorm v*C/η)*(1+Real.exp (2*L))^α*(s : ℝ)^(α-1) := by
  have hspos : 0 < (s : ℝ) := by linarith
  have hsnn : 0 ≤ (s : ℝ) := hspos.le
  have hbase : 1 + Real.exp (2 * L) * (s : ℝ) ≤
      (1 + Real.exp (2 * L)) * (s : ℝ) := by nlinarith
  have hp := Real.rpow_le_rpow (by positivity : 0 ≤ 1 + Real.exp (2 * L) * (s : ℝ)) hbase hα
  have hk : 0 ≤ A + euclideanNorm v * C / η :=
    add_nonneg hA (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hC) hη.le)
  have hs' : 0 < s := by exact_mod_cast hspos
  calc
    _ ≤ (A + euclideanNorm v * C / η) *
        (1 + Real.exp (2 * L) * (s : ℝ)) ^ α / (s : ℝ) :=
      c12_inverse_clock_velocity_error_of_power_error ω γ L hω η C A α hη hC hA hα v hclock hvelocity s hs'
    _ ≤ (A + euclideanNorm v * C / η) *
        ((1 + Real.exp (2 * L)) * (s : ℝ)) ^ α / (s : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hp hk) hsnn
    _ = (A + euclideanNorm v * C / η) * (1 + Real.exp (2 * L)) ^ α *
        (s : ℝ) ^ (α - 1) := by
      rw [Real.mul_rpow (by positivity) hsnn, Real.rpow_sub_one (ne_of_gt hspos)]
      ring

/-- Sublinear polynomial errors imply the velocity limit under the actual inverse clock. -/
theorem c12_inverse_clock_velocity_tendsto_of_power_errors {d : ℕ}
    (ω : FieldPair d) (γ : Path d) (L : ℝ) (hω : IsRegular L ω)
    (η C A α : ℝ) (hη : 0 < η) (hC : 0 ≤ C) (hA : 0 ≤ A)
    (hα : 0 ≤ α) (hαlt : α < 1) (v : Vec d)
    (hclock : ∀ t : ℝ≥0,
      |(Clock.physicalPathClock ω γ t : ℝ)-η*(t : ℝ)| ≤ C*(1+(t : ℝ))^α)
    (hvelocity : ∀ t : ℝ≥0,
      euclideanNorm (γ t-(t : ℝ) • v) ≤ A*(1+(t : ℝ))^α) :
    Tendsto (fun s : ℝ≥0 => (s : ℝ)⁻¹ •
      γ (Clock.InverseMeaningV3.inversePhysicalPathClock ω γ L hω s))
      atTop (𝓝 (η⁻¹ • v)) := by
  have hcoe : Tendsto (fun s : ℝ≥0 => (s : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hpower : Tendsto (fun s : ℝ≥0 => (s : ℝ) ^ (α - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hαlt)).comp hcoe
  have hbound := hpower.const_mul ((A + euclideanNorm v * C / η) *
    (1 + Real.exp (2 * L)) ^ α)
  have hnorm (x : Vec d) : ‖x‖ ≤ euclideanNorm x := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs]
    apply Real.abs_le_sqrt
    change x i ^ 2 ≤ ∑ j, x j * x j
    simpa only [pow_two] using! Finset.single_le_sum
      (fun j _ => mul_self_nonneg (x j)) (Finset.mem_univ i)
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) _
    (by simpa only [mul_zero] using hbound)
  filter_upwards [hcoe.eventually (eventually_ge_atTop 1)] with s hs
  exact (hnorm _).trans
    (c12_inverse_clock_velocity_power_rate ω γ L hω η C A α hη hC hA hα v hclock hvelocity s hs)


/-- Uniform velocity convergence for a family with common sublinear error bounds. -/
theorem c12_uniform_inverse_clock_velocity_of_power_errors {A : Type*} {d : ℕ}
    (ω : A → FieldPair d) (γ : A → Path d) (L : ℝ)
    (hω : ∀ a, IsRegular L (ω a)) (η : A → ℝ) (v : A → Vec d)
    (ηmin C B V α : ℝ) (hηmin : 0 < ηmin) (hη : ∀ a, ηmin ≤ η a)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hv : ∀ a, euclideanNorm (v a) ≤ V) (hα : 0 ≤ α) (hα1 : α < 1)
    (hclock : ∀ a (t : ℝ≥0),
      |(Clock.physicalPathClock (ω a) (γ a) t : ℝ)-η a*(t : ℝ)| ≤ C*(1+(t : ℝ))^α)
    (hvelocity : ∀ a (t : ℝ≥0),
      euclideanNorm (γ a t-(t : ℝ) • v a) ≤ B*(1+(t : ℝ))^α) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ s : ℝ≥0 in atTop, ∀ a,
      euclideanNorm ((s : ℝ)⁻¹ • γ a
        (Clock.InverseMeaningV3.inversePhysicalPathClock (ω a) (γ a) L (hω a) s)-
          (η a)⁻¹ • v a) ≤ ε := by
  have hcoe : Tendsto (fun s : ℝ≥0 => (s : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hpower : Tendsto (fun s : ℝ≥0 => (s : ℝ) ^ (α - 1)) atTop (𝓝 0) := by
    simpa only [neg_sub, Function.comp_def] using
      (tendsto_rpow_neg_atTop (sub_pos.mpr hα1)).comp hcoe
  have hbound : Tendsto (fun s : ℝ≥0 =>
      (B + V * C / ηmin) * (1 + Real.exp (2 * L)) ^ α *
        (s : ℝ) ^ (α - 1)) atTop (𝓝 0) := by
    simpa only [mul_zero] using hpower.const_mul
      ((B + V * C / ηmin) * (1 + Real.exp (2 * L)) ^ α)
  intro ε hε
  filter_upwards [hcoe.eventually (eventually_ge_atTop 1),
    hbound.eventually (Iio_mem_nhds hε)] with s hs hsmall
  intro a
  have hηa : 0 < η a := lt_of_lt_of_le hηmin (hη a)
  have hnum : euclideanNorm (v a) * C ≤ V * C :=
    mul_le_mul_of_nonneg_right (hv a) hC
  have hdiv : euclideanNorm (v a) * C / η a ≤ V * C / ηmin := by
    calc
      _ ≤ V * C / η a := div_le_div_of_nonneg_right hnum hηa.le
      _ ≤ V * C / ηmin := div_le_div_of_nonneg_left (mul_nonneg hV hC) hηmin (hη a)
  have hfactor : B + euclideanNorm (v a) * C / η a ≤ B + V * C / ηmin :=
    add_le_add_right hdiv B
  have hpow : 0 ≤ (1 + Real.exp (2 * L)) ^ α * (s : ℝ) ^ (α - 1) :=
    mul_nonneg (Real.rpow_nonneg (by positivity) _) (Real.rpow_nonneg (by positivity) _)
  calc
    _ ≤ (B + euclideanNorm (v a) * C / η a) * (1 + Real.exp (2 * L)) ^ α *
        (s : ℝ) ^ (α - 1) :=
      c12_inverse_clock_velocity_power_rate (ω a) (γ a) L (hω a) (η a) C B α
        hηa hC hB hα (v a) (hclock a) (hvelocity a) s hs
    _ ≤ (B + V * C / ηmin) * (1 + Real.exp (2 * L)) ^ α *
        (s : ℝ) ^ (α - 1) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hfactor hpow
    _ ≤ ε := le_of_lt hsmall


/-- A common power bound holds uniformly over every later inverse-clock time. -/
theorem c12_uniform_inverse_clock_velocity_maximal_power_bound {A : Type*} {d : ℕ}
    (ω : A → FieldPair d) (γ : A → Path d) (L : ℝ)
    (hω : ∀ a, IsRegular L (ω a)) (η : A → ℝ) (v : A → Vec d)
    (ηmin C B V α : ℝ) (hηmin : 0 < ηmin) (hη : ∀ a, ηmin ≤ η a)
    (hC : 0 ≤ C) (hB : 0 ≤ B) (hV : 0 ≤ V)
    (hv : ∀ a, euclideanNorm (v a) ≤ V) (hα : 0 ≤ α) (hα1 : α < 1)
    (hclock : ∀ a (t : ℝ≥0),
      |(Clock.physicalPathClock (ω a) (γ a) t : ℝ)-η a*(t : ℝ)| ≤ C*(1+(t : ℝ))^α)
    (hvelocity : ∀ a (t : ℝ≥0),
      euclideanNorm (γ a t-(t : ℝ) • v a) ≤ B*(1+(t : ℝ))^α) :
    ∀ r : ℝ≥0, 1 ≤ (r : ℝ) → ∀ s : ℝ≥0, r ≤ s → ∀ a,
      euclideanNorm ((s : ℝ)⁻¹ • γ a
        (Clock.InverseMeaningV3.inversePhysicalPathClock (ω a) (γ a) L (hω a) s)-
        (η a)⁻¹ • v a) ≤
      (B+V*C/ηmin)*(1+Real.exp (2*L))^α*(r : ℝ)^(α-1) := by
  intro r hr s hrs a
  have hrs' : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
  have hs : 1 ≤ (s : ℝ) := le_trans hr hrs'
  have hηa : 0 < η a := lt_of_lt_of_le hηmin (hη a)
  have hdiv : euclideanNorm (v a) * C / η a ≤ V * C / ηmin := by
    calc
      _ ≤ V * C / η a := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (hv a) hC) hηa.le
      _ ≤ V * C / ηmin := div_le_div_of_nonneg_left (mul_nonneg hV hC) hηmin (hη a)
  have hfactor : B + euclideanNorm (v a) * C / η a ≤ B + V * C / ηmin :=
    add_le_add_right hdiv B
  have hbase : 0 ≤ (1 + Real.exp (2 * L)) ^ α := Real.rpow_nonneg (by positivity) _
  have hspow : 0 ≤ (s : ℝ) ^ (α - 1) := Real.rpow_nonneg (by linarith) _
  have hp : (s : ℝ) ^ (α - 1) ≤ (r : ℝ) ^ (α - 1) :=
    Real.rpow_le_rpow_of_nonpos (by linarith) hrs' (by linarith)
  have hcommon : 0 ≤ (B + V * C / ηmin) * (1 + Real.exp (2 * L)) ^ α :=
    mul_nonneg (add_nonneg hB (div_nonneg (mul_nonneg hV hC) hηmin.le)) hbase
  calc
    _ ≤ (B + euclideanNorm (v a) * C / η a) * (1 + Real.exp (2 * L)) ^ α *
        (s : ℝ) ^ (α - 1) :=
      c12_inverse_clock_velocity_power_rate (ω a) (γ a) L (hω a) (η a) C B α
        hηa hC hB hα (v a) (hclock a) (hvelocity a) s hs
    _ ≤ (B + V * C / ηmin) * (1 + Real.exp (2 * L)) ^ α *
        (s : ℝ) ^ (α - 1) := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hfactor (mul_nonneg hbase hspow)
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hcommon

/-- A square-integrable random power envelope controls the maximal inverse velocity. -/
theorem c12_inverse_velocity_maximal_tail_of_random_power_errors {d : ℕ} {L : ℝ}
 (μ : Measure (ReductionImageV3.PhysicalField d L × Path d))
 (η : ℝ) (hη : 0 < η) (v : Vec d) (α : ℝ) (hα : 0 ≤ α) (hα1 : α < 1)
 (C B : ReductionImageV3.PhysicalField d L × Path d → ℝ)
 (hC : ∀ z, 0 ≤ C z) (hB : ∀ z, 0 ≤ B z)
 (hM : MemLp (fun z => B z+euclideanNorm v*C z/η) 2 μ)
 (hclock : ∀ᵐ z ∂μ, ∀ t : ℝ≥0,
  |(Clock.physicalPathClock z.1.1 z.2 t : ℝ)-η*(t : ℝ)| ≤ C z*(1+(t : ℝ))^α)
 (hvelocity : ∀ᵐ z ∂μ, ∀ t : ℝ≥0,
  euclideanNorm (z.2 t-(t : ℝ) • v) ≤ B z*(1+(t : ℝ))^α)
 (r : ℝ≥0) (hr : 1 ≤ (r : ℝ)) (ε : ℝ) (hε : 0 < ε) :
 μ {z | ∃ s : ℝ≥0, r ≤ s ∧ ε < euclideanNorm
   ((s : ℝ)⁻¹ • z.2 (Clock.PathMapV4.inversePhysicalTime z s)-η⁻¹ • v)}
 ≤ ENNReal.ofReal
  (((1+Real.exp (2*L))^α*(r : ℝ)^(α-1))^2*
   (∫ z, (B z+euclideanNorm v*C z/η)^2 ∂μ)/ε^2) := by
  let K : ℝ := (1+Real.exp (2*L))^α*(r : ℝ)^(α-1)
  let F : ReductionImageV3.PhysicalField d L × Path d → ℝ :=
    fun z => B z+euclideanNorm v*C z/η
  have hK : 0 ≤ K := mul_nonneg (Real.rpow_nonneg (by positivity) _)
    (Real.rpow_nonneg (by linarith) _)
  have hF : ∀ z, 0 ≤ F z := fun z => add_nonneg (hB z)
    (div_nonneg (mul_nonneg (Real.sqrt_nonneg _) (hC z)) hη.le)
  have hbound : ∀ᵐ z ∂μ, ∀ s : ℝ≥0, r ≤ s →
      euclideanNorm ((s : ℝ)⁻¹ • z.2 (Clock.PathMapV4.inversePhysicalTime z s)-η⁻¹ • v)
        ≤ F z * K := by
    filter_upwards [hclock, hvelocity] with z hc hv
    intro s hrs
    have hrs' : (r : ℝ) ≤ (s : ℝ) := by exact_mod_cast hrs
    have hs : 1 ≤ (s : ℝ) := le_trans hr hrs'
    have hp : (s : ℝ) ^ (α - 1) ≤ (r : ℝ) ^ (α - 1) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) hrs' (by linarith)
    have hb := c12_inverse_clock_velocity_power_rate z.1.1 z.2 L z.1.2 η (C z) (B z) α
      hη (hC z) (hB z) hα v hc hv s hs
    change euclideanNorm ((s : ℝ)⁻¹ • z.2
      (Clock.InverseMeaningV3.inversePhysicalPathClock z.1.1 z.2 L z.1.2 s)-η⁻¹ • v) ≤ _
    calc
      _ ≤ F z * (1+Real.exp (2*L))^α * (s : ℝ)^(α-1) := hb
      _ ≤ F z * K := by
        dsimp [K]
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp
          (mul_nonneg (hF z)
            (Real.rpow_nonneg (show 0 ≤ 1 + Real.exp (2 * L) by positivity) α))
  have hi : Integrable (fun z => (K * F z)^2) μ := by
    simpa only [mul_pow] using hM.integrable_sq.const_mul (K^2)
  have hm : AEMeasurable (fun z => ENNReal.ofReal ((K * F z)^2)) μ :=
    ENNReal.measurable_ofReal.comp_aemeasurable hi.aestronglyMeasurable.aemeasurable
  have hmark := meas_ge_le_lintegral_div hm (ε := ENNReal.ofReal (ε^2))
    (ENNReal.ofReal_pos.2 (pow_pos hε 2)).ne' ENNReal.ofReal_ne_top
  have hsub : {z | ∃ s : ℝ≥0, r ≤ s ∧ ε < euclideanNorm
      ((s : ℝ)⁻¹ • z.2 (Clock.PathMapV4.inversePhysicalTime z s)-η⁻¹ • v)} ≤ᵐ[μ]
      {z | ENNReal.ofReal (ε^2) ≤ ENNReal.ofReal ((K * F z)^2)} := by
    filter_upwards [hbound] with z hz
    rintro ⟨s, hrs, hs⟩
    apply ENNReal.ofReal_le_ofReal
    have hh : ε ≤ K * F z := by nlinarith [hz s hrs]
    exact pow_le_pow_left₀ hε.le hh 2
  calc
    _ ≤ μ {z | ENNReal.ofReal (ε^2) ≤ ENNReal.ofReal ((K * F z)^2)} := measure_mono_ae hsub
    _ ≤ (∫⁻ z, ENNReal.ofReal ((K * F z)^2) ∂μ) / ENNReal.ofReal (ε^2) := hmark
    _ = ENNReal.ofReal ((K^2 * ∫ z, (F z)^2 ∂μ) / ε^2) := by
      rw [← ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun z => sq_nonneg _),
        ← ENNReal.ofReal_div_of_pos (pow_pos hε 2)]
      congr 1
      simp only [mul_pow, integral_const_mul]
    _ = _ := rfl

/-- Centering the actual clock is the time integral of its centered density. -/
theorem c12_physical_clock_centered_integral {d : ℕ} {L : ℝ}
    (z : ReductionImageV3.PhysicalField d L × Path d) (η : ℝ)
    (T : ℝ≥0) (hT : 0 < T) :
    (Clock.physicalPathClock z.1.1 z.2 T : ℝ) / (T : ℝ) - η =
      (T : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(T : ℝ),
        (Real.exp (-2 * z.1.1.2 (z.2 s.toNNReal)) - η) := by
  have ht : (T : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hT)
  have hi : IntervalIntegrable
      (fun s : ℝ => Real.exp (-2 * z.1.1.2 (z.2 s.toNNReal))) volume 0 (T : ℝ) :=
    Clock.continuous_clockDensity_along z.1.1 z.2 |>.intervalIntegrable _ _
  rw [Clock.InverseMeaningV3.coe_physicalPathClock_explicit,
    intervalIntegral.integral_sub hi intervalIntegrable_const]
  simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  field_simp <;> ring

/-- Regularity bounds the centered physical clock density uniformly in time and sample. -/
theorem c12_centered_clock_density_bound {d : ℕ} {L : ℝ}
    (z : ReductionImageV3.PhysicalField d L × Path d) (η s : ℝ) :
    |Real.exp (-2 * z.1.1.2 (z.2 s.toNNReal)) - η| ≤ Real.exp (2 * L) + |η| := by
  have hb := (clockDensity_bounds z.1.1 (z.2 s.toNNReal) L
    (z.1.2.2.1 (z.2 s.toNNReal))).2
  change Real.exp (-2 * z.1.1.2 (z.2 s.toNNReal)) ≤ Real.exp (2 * L) at hb
  calc
    |Real.exp (-2 * z.1.1.2 (z.2 s.toNNReal)) - η| ≤
        |Real.exp (-2 * z.1.1.2 (z.2 s.toNNReal))| + |η| := abs_sub _ _
    _ ≤ Real.exp (2 * L) + |η| := by
      rw [abs_of_pos (Real.exp_pos _)]
      exact add_le_add hb le_rfl

/-- The actual clock's second moment is the double time integral of its joint correlation. -/
theorem c12_physical_clock_l2_eq_double_correlation {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ) (T : ℝ≥0) (hT : 0 < T) :
    (∫ z : ReductionImageV3.PhysicalField d L × Path d,
      ((Clock.physicalPathClock z.1.1 z.2 T : ℝ)/(T : ℝ)-η)^2 ∂μ) =
    (T : ℝ)⁻¹^2 * ∫ s in (0 : ℝ)..(T : ℝ), ∫ u in (0 : ℝ)..(T : ℝ),
      ∫ z : ReductionImageV3.PhysicalField d L × Path d,
        (Real.exp (-2*z.1.1.2 (z.2 s.toNNReal))-η)*
        (Real.exp (-2*z.1.1.2 (z.2 u.toNNReal))-η) ∂μ := by
  let Z := ReductionImageV3.PhysicalField d L × Path d
  let f : Z → ℝ → ℝ := fun z s => Real.exp (-2*z.1.1.2 (z.2 s.toNNReal))-η
  let I : Z → ℝ := fun z => ∫ u in (0 : ℝ)..(T : ℝ), f z u
  let K : ℝ := Real.exp (2 * L) + |η|
  have hK : 0 ≤ K := add_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hf : Continuous (fun p : ℝ × Z => f p.2 p.1) := by
    have hc := Clock.continuous_clockDensity_time_path (d := d)
    exact (hc.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd.fst).prodMk continuous_snd.snd))).sub
      continuous_const
  have hb : ∀ z s, ‖f z s‖ ≤ K := by
    intro z s
    simpa only [Real.norm_eq_abs] using c12_centered_clock_density_bound z η s
  have hI : Continuous I := by
    have hc : Continuous (fun z : Z => (Clock.physicalPathClock z.1.1 z.2 T : ℝ)) :=
      (Clock.continuous_physicalPathClock_at (d := d) T).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    have heq : I = fun z : Z => (Clock.physicalPathClock z.1.1 z.2 T : ℝ) - (T : ℝ) * η := by
      funext z
      dsimp [I, f]
      change (∫ u in (0 : ℝ)..(T : ℝ), clockDensity z.1.1 (z.2 u.toNNReal) - η) = _
      rw [intervalIntegral.integral_sub
        (Clock.continuous_clockDensity_along z.1.1 z.2 |>.intervalIntegrable _ _)
        intervalIntegrable_const]
      change (∫ u in (0 : ℝ)..(T : ℝ), clockDensity z.1.1 (z.2 u.toNNReal)) -
        (∫ u in (0 : ℝ)..(T : ℝ), η) =
        (Clock.physicalPathClock z.1.1 z.2 T : ℝ) - (T : ℝ) * η
      rw [Clock.InverseMeaningV3.coe_physicalPathClock_explicit]
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, clockDensity]
    rw [heq]
    exact hc.sub continuous_const
  have hIb : ∀ z, ‖I z‖ ≤ K * (T : ℝ) := by
    intro z
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (T : ℝ)) (f := f z) (C := K)
      (fun s _ => hb z s)
    simpa only [sub_zero, abs_of_nonneg T.coe_nonneg] using hh
  have hfin : (volume : Measure ℝ) (Set.uIoc (0 : ℝ) (T : ℝ)) ≠ ⊤ := by
    rw [Set.uIoc_of_le T.coe_nonneg, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  let ν := (volume : Measure ℝ).restrict (Set.uIoc (0 : ℝ) (T : ℝ))
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hfin
  have hfirst : Integrable (fun p : ℝ × Z => f p.2 p.1 * I p.2) (ν.prod μ) := by
    apply Integrable.of_bound (hf.mul (hI.comp continuous_snd)).aestronglyMeasurable
      (K * (K * (T : ℝ)))
    filter_upwards with p
    change ‖f p.2 p.1 * I p.2‖ ≤ K * (K * (T : ℝ))
    rw [norm_mul]
    exact mul_le_mul (hb p.2 p.1) (hIb p.2) (norm_nonneg _) hK
  have hsecond (s : ℝ) : Integrable (fun p : ℝ × Z => f p.2 s * f p.2 p.1)
      (ν.prod μ) := by
    have hs : Continuous (fun p : ℝ × Z => f p.2 s) :=
      hf.comp (continuous_const.prodMk continuous_snd)
    apply Integrable.of_bound (hs.mul hf).aestronglyMeasurable (K * K)
    filter_upwards with p
    change ‖f p.2 s * f p.2 p.1‖ ≤ K * K
    rw [norm_mul]
    exact mul_le_mul (hb p.2 s) (hb p.2 p.1) (norm_nonneg _) hK
  calc
    _ = (T : ℝ)⁻¹^2 * ∫ z : Z, (∫ s in (0 : ℝ)..(T : ℝ), f z s * I z) ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      filter_upwards with z
      rw [c12_physical_clock_centered_integral z η T hT, mul_pow]
      congr 1
      simp only [I, f, intervalIntegral.integral_mul_const, pow_two]
    _ = (T : ℝ)⁻¹^2 * ∫ s in (0 : ℝ)..(T : ℝ), ∫ z : Z, f z s * I z ∂μ := by
      congr 1
      exact (intervalIntegral_integral_swap hfirst).symm
    _ = _ := by
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      simp only [I, ← intervalIntegral.integral_const_mul]
      exact (intervalIntegral_integral_swap (hsecond s)).symm

/-- The normalized primitive of a power-decay kernel vanishes at infinity. -/
theorem c12_power_kernel_primitive_tendsto_zero (α : ℝ) (hα : 0 < α) :
    Tendsto (fun T : ℝ≥0 => ((1 + (T : ℝ)) ^ (1 - α) - 1) / (T : ℝ))
      atTop (𝓝 0) := by
  have ht : Tendsto (fun T : ℝ≥0 => (T : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr tendsto_id
  have hp : Tendsto (fun T : ℝ≥0 => (1 + (T : ℝ)) ^ (-α)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop hα).comp (tendsto_const_nhds.add_atTop ht)
  have hi : Tendsto (fun T : ℝ≥0 => ((T : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp ht
  have hlim : Tendsto (fun T : ℝ≥0 => (1 + (T : ℝ)) ^ (-α) *
      (1 + (T : ℝ)⁻¹) - (T : ℝ)⁻¹) atTop (𝓝 0) := by
    simpa only [add_zero, mul_one, sub_zero] using
      (hp.mul ((tendsto_const_nhds : Tendsto (fun _ : ℝ≥0 => (1 : ℝ)) atTop (𝓝 1)).add hi)).sub hi
  have heq : (fun T : ℝ≥0 => ((1 + (T : ℝ)) ^ (1 - α) - 1) / (T : ℝ)) =ᶠ[atTop]
      (fun T : ℝ≥0 => (1 + (T : ℝ)) ^ (-α) * (1 + (T : ℝ)⁻¹) - (T : ℝ)⁻¹) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with T hT
    have hpos : 0 < (T : ℝ) := by exact_mod_cast hT
    have hbase : 0 < 1 + (T : ℝ) := by positivity
    rw [show 1 - α = 1 + (-α) by ring, Real.rpow_add hbase, Real.rpow_one]
    field_simp
    <;> ring
  convert hlim.congr' heq.symm using 1 <;> norm_num

/-- The integral of the separation kernel over an interval is bounded by two
copies of its integral from zero. -/
theorem c12_power_kernel_interval_bound (α T s : ℝ)
    (hs0 : 0 ≤ s) (hsT : s ≤ T) :
    (∫ u in (0 : ℝ)..T, (1 + |s - u|) ^ (-α)) ≤
      2 * ∫ u in (0 : ℝ)..T, (1 + |u|) ^ (-α) := by
  let k : ℝ → ℝ := fun x => (1 + |x|) ^ (-α)
  have hk : Continuous k := by
    apply (continuous_const.add continuous_id.abs).rpow_const
    intro x
    left
    have : 0 < 1 + |x| := by positivity
    exact ne_of_gt this
  have hnonneg : ∀ x, 0 ≤ k x := fun x => Real.rpow_nonneg (by positivity) _
  have hleft : (∫ u in (0 : ℝ)..s, (1 + |s - u|) ^ (-α)) =
      ∫ u in (0 : ℝ)..s, k u := by
    calc
      _ = ∫ u in (0 : ℝ)..s, k (s - u) := rfl
      _ = ∫ u in s - s..s - 0, k u := intervalIntegral.integral_comp_sub_left k s
      _ = _ := by simp
  have hright : (∫ u in s..T, (1 + |s - u|) ^ (-α)) =
      ∫ u in (0 : ℝ)..(T-s), k u := by
    calc
      _ = ∫ u in s..T, k (u-s) := by
        apply intervalIntegral.integral_congr
        intro u hu
        dsimp [k]
        rw [abs_sub_comm]
      _ = ∫ u in s-s..T-s, k u := intervalIntegral.integral_comp_sub_right k s
      _ = _ := by simp
  have hbound1 : (∫ u in (0 : ℝ)..s, k u) ≤ ∫ u in (0 : ℝ)..T, k u :=
    intervalIntegral.integral_mono_interval le_rfl hs0 hsT
      (ae_of_all _ hnonneg) (hk.intervalIntegrable _ _)
  have hbound2 : (∫ u in (0 : ℝ)..(T-s), k u) ≤ ∫ u in (0 : ℝ)..T, k u :=
    intervalIntegral.integral_mono_interval le_rfl (sub_nonneg.mpr hsT) (by linarith)
      (ae_of_all _ hnonneg) (hk.intervalIntegrable _ _)
  have hc : Continuous (fun u : ℝ => (1 + |s - u|) ^ (-α)) := by
    apply (continuous_const.add (continuous_const.sub continuous_id).abs).rpow_const
    intro x
    left
    have : 0 < 1 + |s - x| := by positivity
    exact ne_of_gt this
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (hc.intervalIntegrable 0 s) (hc.intervalIntegrable s T), hleft, hright]
  linarith

/-- The power kernel has an explicit primitive on a nonnegative interval. -/
theorem c12_power_kernel_integral (α T : ℝ) (hα1 : α < 1) (hT : 0 ≤ T) :
    (∫ u in (0 : ℝ)..T, (1 + |u|) ^ (-α)) =
      ((1 + T) ^ (1 - α) - 1) / (1 - α) := by
  have heq : (∫ u in (0 : ℝ)..T, (1 + |u|) ^ (-α)) =
      ∫ u in (0 : ℝ)..T, (1 + u) ^ (-α) := by
    apply intervalIntegral.integral_congr
    intro u hu
    have hu0 : 0 ≤ u := ((Set.uIcc_of_le hT) ▸ hu).1
    dsimp only
    rw [abs_of_nonneg hu0]
  have htrans : (∫ u in (0 : ℝ)..T, (1 + u) ^ (-α)) =
      ∫ u in (1 : ℝ)..(1 + T), u ^ (-α) := by
    simpa only [add_zero] using
      (intervalIntegral.integral_comp_add_left (fun u : ℝ => u ^ (-α)) (a := 0) (b := T) 1)
  rw [heq, htrans]
  rw [integral_rpow (Or.inl (by linarith : -1 < -α))]
  simp only [Real.one_rpow]
  congr 1 <;> ring

/-- A correlation dominated by the power kernel has a controlled double integral. -/
theorem c12_correlation_double_integral_bound (q : ℝ → ℝ → ℝ) (C α T : ℝ)
    (hC : 0 ≤ C) (hα1 : α < 1) (hT : 0 ≤ T)
    (hrow : ∀ s, IntervalIntegrable (q s) volume 0 T)
    (houter : IntervalIntegrable (fun s => ∫ u in (0 : ℝ)..T, q s u) volume 0 T)
    (hbound : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ u ∈ Set.Icc (0 : ℝ) T,
      q s u ≤ C * (1 + |s-u|) ^ (-α)) :
    (∫ s in (0 : ℝ)..T, ∫ u in (0 : ℝ)..T, q s u) ≤
      T * (2 * C * (((1+T) ^ (1-α)-1) / (1-α))) := by
  have hinner : ∀ s ∈ Set.Icc (0 : ℝ) T,
      (∫ u in (0 : ℝ)..T, q s u) ≤
        2 * C * (((1+T) ^ (1-α)-1) / (1-α)) := by
    intro s hs
    have hc : Continuous (fun u : ℝ => C * (1 + |s-u|) ^ (-α)) := by
      apply continuous_const.mul
      apply (continuous_const.add (continuous_const.sub continuous_id).abs).rpow_const
      intro x
      left
      have : 0 < 1 + |s-x| := by positivity
      exact ne_of_gt this
    calc
      _ ≤ ∫ u in (0 : ℝ)..T, C * (1 + |s-u|) ^ (-α) :=
        intervalIntegral.integral_mono_on hT (hrow s) (hc.intervalIntegrable _ _)
          (hbound s hs)
      _ = C * ∫ u in (0 : ℝ)..T, (1 + |s-u|) ^ (-α) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ C * (2 * ∫ u in (0 : ℝ)..T, (1 + |u|) ^ (-α)) :=
        mul_le_mul_of_nonneg_left (c12_power_kernel_interval_bound α T s hs.1 hs.2) hC
      _ = _ := by rw [c12_power_kernel_integral α T hα1 hT]; ring
  calc
    _ ≤ ∫ _s in (0 : ℝ)..T, 2 * C * (((1+T) ^ (1-α)-1) / (1-α)) :=
      intervalIntegral.integral_mono_on hT houter intervalIntegrable_const hinner
    _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]

/-- The actual clock correlations are integrable in both time variables. -/
theorem c12_clock_correlation_interval_integrable {d : ℕ} {L : ℝ}
    (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
    (η : ℝ) (T : ℝ≥0) :
    let q : ℝ → ℝ → ℝ := fun s u => ∫ z : ReductionImageV3.PhysicalField d L × Path d,
      (Real.exp (-2*z.1.1.2 (z.2 s.toNNReal))-η) *
      (Real.exp (-2*z.1.1.2 (z.2 u.toNNReal))-η) ∂μ
    (∀ s, IntervalIntegrable (q s) volume 0 (T : ℝ)) ∧
      IntervalIntegrable (fun s => ∫ u in (0 : ℝ)..(T : ℝ), q s u) volume 0 (T : ℝ) := by
  let Z := ReductionImageV3.PhysicalField d L × Path d
  let f : Z → ℝ → ℝ := fun z s => Real.exp (-2*z.1.1.2 (z.2 s.toNNReal))-η
  let I : Z → ℝ := fun z => ∫ u in (0 : ℝ)..(T : ℝ), f z u
  let K : ℝ := Real.exp (2 * L) + |η|
  have hK : 0 ≤ K := add_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hf : Continuous (fun p : ℝ × Z => f p.2 p.1) := by
    have hc := Clock.continuous_clockDensity_time_path (d := d)
    exact (hc.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd.fst).prodMk continuous_snd.snd))).sub
      continuous_const
  have hb : ∀ z s, ‖f z s‖ ≤ K := by
    intro z s
    simpa only [Real.norm_eq_abs] using c12_centered_clock_density_bound z η s
  have hI : Continuous I := by
    have hc : Continuous (fun z : Z => (Clock.physicalPathClock z.1.1 z.2 T : ℝ)) :=
      (Clock.continuous_physicalPathClock_at (d := d) T).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    have heq : I = fun z : Z => (Clock.physicalPathClock z.1.1 z.2 T : ℝ) - (T : ℝ) * η := by
      funext z
      dsimp [I, f]
      change (∫ u in (0 : ℝ)..(T : ℝ), clockDensity z.1.1 (z.2 u.toNNReal) - η) = _
      rw [intervalIntegral.integral_sub
        (Clock.continuous_clockDensity_along z.1.1 z.2 |>.intervalIntegrable _ _)
        intervalIntegrable_const]
      change (∫ u in (0 : ℝ)..(T : ℝ), clockDensity z.1.1 (z.2 u.toNNReal)) -
        (∫ u in (0 : ℝ)..(T : ℝ), η) =
        (Clock.physicalPathClock z.1.1 z.2 T : ℝ) - (T : ℝ) * η
      rw [Clock.InverseMeaningV3.coe_physicalPathClock_explicit]
      simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, clockDensity]
    rw [heq]
    exact hc.sub continuous_const
  have hIb : ∀ z, ‖I z‖ ≤ K * (T : ℝ) := by
    intro z
    have hh := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := (T : ℝ)) (f := f z) (C := K) (fun s _ => hb z s)
    simpa only [sub_zero, abs_of_nonneg T.coe_nonneg] using hh
  have hfin : (volume : Measure ℝ) (Set.uIoc (0 : ℝ) (T : ℝ)) ≠ ⊤ := by
    rw [Set.uIoc_of_le T.coe_nonneg, Real.volume_Ioc]
    exact ENNReal.ofReal_ne_top
  let ν := (volume : Measure ℝ).restrict (Set.uIoc (0 : ℝ) (T : ℝ))
  haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hfin
  have hfirst : Integrable (fun p : ℝ × Z => f p.2 p.1 * I p.2) (ν.prod μ) := by
    apply Integrable.of_bound (hf.mul (hI.comp continuous_snd)).aestronglyMeasurable
      (K * (K * (T : ℝ)))
    filter_upwards with p
    change ‖f p.2 p.1 * I p.2‖ ≤ K * (K * (T : ℝ))
    rw [norm_mul]
    exact mul_le_mul (hb p.2 p.1) (hIb p.2) (norm_nonneg _) hK
  have hsecond (s : ℝ) : Integrable (fun p : ℝ × Z => f p.2 s * f p.2 p.1)
      (ν.prod μ) := by
    have hs : Continuous (fun p : ℝ × Z => f p.2 s) :=
      hf.comp (continuous_const.prodMk continuous_snd)
    apply Integrable.of_bound (hs.mul hf).aestronglyMeasurable (K * K)
    filter_upwards with p
    change ‖f p.2 s * f p.2 p.1‖ ≤ K * K
    rw [norm_mul]
    exact mul_le_mul (hb p.2 s) (hb p.2 p.1) (norm_nonneg _) hK
  constructor
  · intro s
    exact intervalIntegrable_iff.mpr (hsecond s).integral_prod_left
  · apply intervalIntegrable_iff.mpr
    change Integrable (fun s => ∫ u in (0 : ℝ)..(T : ℝ),
      ∫ z : Z, f z s * f z u ∂μ) ν
    have heq : (fun s => ∫ u in (0 : ℝ)..(T : ℝ),
        ∫ z : Z, f z s * f z u ∂μ) =
        (fun s => ∫ z : Z, f z s * I z ∂μ) := by
      funext s
      simp only [I, ← intervalIntegral.integral_const_mul]
      exact intervalIntegral_integral_swap (hsecond s)
    rw [heq]
    exact hfirst.integral_prod_left

/-- Power decay of the actual joint correlation implies L² convergence of the clock. -/
theorem c12_physical_clock_l2_tendsto_zero_of_correlation_decay {d : ℕ} {L : ℝ}
 (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
 (η C α : ℝ) (hC : 0 ≤ C) (hα : 0 < α) (hα1 : α < 1)
 (hcorr : ∀ s u : ℝ≥0,
  |∫ z : ReductionImageV3.PhysicalField d L × Path d,
   (Real.exp (-2*z.1.1.2 (z.2 s))-η)*
   (Real.exp (-2*z.1.1.2 (z.2 u))-η) ∂μ| ≤
   C*(1+|(s : ℝ)-(u : ℝ)|)^(-α)) :
 Tendsto (fun T : ℝ≥0 => ∫ z : ReductionImageV3.PhysicalField d L × Path d,
  ((Clock.physicalPathClock z.1.1 z.2 T : ℝ)/(T : ℝ)-η)^2 ∂μ)
  atTop (𝓝 0) := by
  let Z := ReductionImageV3.PhysicalField d L × Path d
  let q : ℝ → ℝ → ℝ := fun s u => ∫ z : Z,
    (Real.exp (-2*z.1.1.2 (z.2 s.toNNReal))-η)*
    (Real.exp (-2*z.1.1.2 (z.2 u.toNNReal))-η) ∂μ
  have hlim : Tendsto (fun T : ℝ≥0 => (2*C/(1-α)) *
      (((1+(T : ℝ))^(1-α)-1)/(T : ℝ))) atTop (𝓝 0) := by
    simpa only [mul_zero] using
      (tendsto_const_nhds.mul (c12_power_kernel_primitive_tendsto_zero α hα))
  apply squeeze_zero' (g := fun T : ℝ≥0 => (2*C/(1-α)) *
      (((1+(T : ℝ))^(1-α)-1)/(T : ℝ)))
  · exact Filter.Eventually.of_forall fun T => integral_nonneg fun z => sq_nonneg _
  · filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with T hT
    have hT' : 0 < (T : ℝ) := by exact_mod_cast hT
    have hint := c12_clock_correlation_interval_integrable μ η T
    have hb : ∀ s ∈ Set.Icc (0 : ℝ) (T : ℝ), ∀ u ∈ Set.Icc (0 : ℝ) (T : ℝ),
        q s u ≤ C * (1 + |s-u|) ^ (-α) := by
      intro s hs u hu
      have h := hcorr s.toNNReal u.toNNReal
      rw [Real.coe_toNNReal _ hs.1, Real.coe_toNNReal _ hu.1] at h
      exact le_trans (le_abs_self _) h
    have hd := c12_correlation_double_integral_bound q C α (T : ℝ) hC hα1
      T.coe_nonneg hint.1 hint.2 hb
    rw [c12_physical_clock_l2_eq_double_correlation μ η T hT]
    change (T : ℝ)⁻¹^2 * (∫ s in (0 : ℝ)..(T : ℝ), ∫ u in (0 : ℝ)..(T : ℝ), q s u) ≤ _
    calc
      _ ≤ (T : ℝ)⁻¹^2 * ((T : ℝ) * (2 * C *
          (((1+(T : ℝ))^(1-α)-1)/(1-α)))) :=
        mul_le_mul_of_nonneg_left hd (sq_nonneg _)
      _ = _ := by
        have htne : (T : ℝ) ≠ 0 := ne_of_gt hT'
        have hane : 1 - α ≠ 0 := ne_of_gt (sub_pos.mpr hα1)
        field_simp
        <;> ring
  · exact hlim


/-- Polynomial decay of correlations gives a quantitative clock variance bound. -/
theorem c12_physical_clock_l2_power_bound_of_correlation_decay {d : ℕ} {L : ℝ}
 (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
 (η C α : ℝ) (hC : 0 ≤ C) (hα : 0 < α) (hα1 : α < 1)
 (hcorr : ∀ s u : ℝ≥0,
  |∫ z : ReductionImageV3.PhysicalField d L × Path d,
   (Real.exp (-2*z.1.1.2 (z.2 s))-η)*
   (Real.exp (-2*z.1.1.2 (z.2 u))-η) ∂μ| ≤
   C*(1+|(s : ℝ)-(u : ℝ)|)^(-α)) :
 ∀ T : ℝ≥0, 1 ≤ (T : ℝ) →
 (∫ z : ReductionImageV3.PhysicalField d L × Path d,
  ((Clock.physicalPathClock z.1.1 z.2 T : ℝ)/(T : ℝ)-η)^2 ∂μ) ≤
  (4*C/(1-α))*Real.rpow (T : ℝ) (-α) := by
  intro T hT
  let Z := ReductionImageV3.PhysicalField d L × Path d
  let q : ℝ → ℝ → ℝ := fun s u => ∫ z : Z,
    (Real.exp (-2*z.1.1.2 (z.2 s.toNNReal))-η)*
    (Real.exp (-2*z.1.1.2 (z.2 u.toNNReal))-η) ∂μ
  have hTpos : 0 < (T : ℝ) := by linarith
  have hTnn : (0 : ℝ≥0) < T := by exact_mod_cast hTpos
  have hint := c12_clock_correlation_interval_integrable μ η T
  have hb : ∀ s ∈ Set.Icc (0 : ℝ) (T : ℝ), ∀ u ∈ Set.Icc (0 : ℝ) (T : ℝ),
      q s u ≤ C * (1 + |s-u|) ^ (-α) := by
    intro s hs u hu
    have h := hcorr s.toNNReal u.toNNReal
    rw [Real.coe_toNNReal _ hs.1, Real.coe_toNNReal _ hu.1] at h
    exact le_trans (le_abs_self _) h
  have hd := c12_correlation_double_integral_bound q C α (T : ℝ) hC hα1
    T.coe_nonneg hint.1 hint.2 hb
  have hp : (1+(T : ℝ)) ^ (1-α) ≤ 2 * (T : ℝ) * (T : ℝ) ^ (-α) := by
    have hbase : 0 < 1 + (T : ℝ) := by positivity
    have hr : (1+(T : ℝ)) ^ (-α) ≤ (T : ℝ) ^ (-α) :=
      Real.rpow_le_rpow_of_nonpos hTpos (by linarith) (by linarith)
    have hrpos : 0 ≤ (T : ℝ) ^ (-α) := Real.rpow_nonneg hTpos.le _
    rw [show 1-α = 1 + (-α) by ring, Real.rpow_add hbase, Real.rpow_one]
    calc
      _ ≤ (1+(T : ℝ)) * (T : ℝ) ^ (-α) := mul_le_mul_of_nonneg_left hr hbase.le
      _ ≤ 2 * (T : ℝ) * (T : ℝ) ^ (-α) := by nlinarith
  have hden : 0 < 1 - α := sub_pos.mpr hα1
  have hscale : 0 ≤ 2*C/(1-α) := div_nonneg (by positivity) hden.le
  have hprim : ((1+(T : ℝ))^(1-α)-1)/(T : ℝ) ≤ 2 * (T : ℝ)^(-α) := by
    apply (div_le_iff₀ hTpos).2
    nlinarith
  have hmain : (∫ z : Z, ((Clock.physicalPathClock z.1.1 z.2 T : ℝ)/(T : ℝ)-η)^2 ∂μ) ≤
      (2*C/(1-α)) * (((1+(T : ℝ))^(1-α)-1)/(T : ℝ)) := by
    rw [c12_physical_clock_l2_eq_double_correlation μ η T hTnn]
    change (T : ℝ)⁻¹^2 * (∫ s in (0 : ℝ)..(T : ℝ), ∫ u in (0 : ℝ)..(T : ℝ), q s u) ≤ _
    calc
      _ ≤ (T : ℝ)⁻¹^2 * ((T : ℝ) * (2 * C *
          (((1+(T : ℝ))^(1-α)-1)/(1-α)))) :=
        mul_le_mul_of_nonneg_left hd (sq_nonneg _)
      _ = _ := by
        have htne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
        have hane : 1 - α ≠ 0 := ne_of_gt hden
        field_simp
        <;> ring
  calc
    _ ≤ (2*C/(1-α)) * (((1+(T : ℝ))^(1-α)-1)/(T : ℝ)) := hmain
    _ ≤ (2*C/(1-α)) * (2 * (T : ℝ)^(-α)) := mul_le_mul_of_nonneg_left hprim hscale
    _ = _ := by rw [Real.rpow_eq_pow]; ring


/-- Critical correlation decay yields a logarithmic clock variance bound. -/
theorem c12_physical_clock_l2_logarithmic_bound_of_critical_correlation_decay {d : ℕ} {L : ℝ}
 (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
 (η C : ℝ) (hC : 0 ≤ C)
 (hcorr : ∀ s u : ℝ≥0,
  |∫ z : ReductionImageV3.PhysicalField d L × Path d,
   (Real.exp (-2*z.1.1.2 (z.2 s))-η)*
   (Real.exp (-2*z.1.1.2 (z.2 u))-η) ∂μ| ≤
   C/(1+|(s : ℝ)-(u : ℝ)|)) :
 ∀ T : ℝ≥0, 1 ≤ (T : ℝ) →
 (∫ z : ReductionImageV3.PhysicalField d L × Path d,
  ((Clock.physicalPathClock z.1.1 z.2 T : ℝ)/(T : ℝ)-η)^2 ∂μ) ≤
  (4*C)*Real.log (1+(T : ℝ))/(T : ℝ) := by
  intro T hT
  let Z := ReductionImageV3.PhysicalField d L × Path d
  let q : ℝ → ℝ → ℝ := fun s u => ∫ z : Z,
    (Real.exp (-2*z.1.1.2 (z.2 s.toNNReal))-η)*
    (Real.exp (-2*z.1.1.2 (z.2 u.toNNReal))-η) ∂μ
  have hTpos : 0 < (T : ℝ) := by linarith
  have hTnn : (0 : ℝ≥0) < T := by exact_mod_cast hTpos
  have hint := c12_clock_correlation_interval_integrable μ η T
  have hk : (∫ u in (0 : ℝ)..(T : ℝ), (1 + |u|) ^ (-(1 : ℝ))) =
      Real.log (1 + (T : ℝ)) := by
    have heq : (∫ u in (0 : ℝ)..(T : ℝ), (1 + |u|) ^ (-(1 : ℝ))) =
        ∫ u in (0 : ℝ)..(T : ℝ), (1 + u)⁻¹ := by
      apply intervalIntegral.integral_congr
      intro u hu
      have hu0 : 0 ≤ u := ((Set.uIcc_of_le T.coe_nonneg) ▸ hu).1
      dsimp only
      rw [abs_of_nonneg hu0]
      simp only [Real.rpow_neg_one]
    rw [heq]
    have ht : (∫ u in (0 : ℝ)..(T : ℝ), (1 + u)⁻¹) =
        ∫ u in (1 : ℝ)..(1 + (T : ℝ)), u⁻¹ := by
      simpa only [add_zero] using
        (intervalIntegral.integral_comp_add_left (fun u : ℝ => u⁻¹) (a := 0) (b := (T : ℝ)) 1)
    rw [ht, integral_inv_of_pos (by norm_num) (by positivity)]
    simp
  have hinner : ∀ s ∈ Set.Icc (0 : ℝ) (T : ℝ),
      (∫ u in (0 : ℝ)..(T : ℝ), q s u) ≤ 2*C*Real.log (1+(T : ℝ)) := by
    intro s hs
    have hc : Continuous (fun u : ℝ => C * (1 + |s-u|) ^ (-(1 : ℝ))) := by
      apply continuous_const.mul
      apply (continuous_const.add (continuous_const.sub continuous_id).abs).rpow_const
      intro x
      left
      have : 0 < 1 + |s-x| := by positivity
      exact ne_of_gt this
    calc
      _ ≤ ∫ u in (0 : ℝ)..(T : ℝ), C * (1 + |s-u|) ^ (-(1 : ℝ)) := by
        apply intervalIntegral.integral_mono_on T.coe_nonneg (hint.1 s) (hc.intervalIntegrable _ _)
        intro u hu
        have h := hcorr s.toNNReal u.toNNReal
        rw [Real.coe_toNNReal _ hs.1, Real.coe_toNNReal _ hu.1] at h
        simpa only [Real.rpow_neg_one, div_eq_mul_inv] using le_trans (le_abs_self _) h
      _ = C * ∫ u in (0 : ℝ)..(T : ℝ), (1 + |s-u|) ^ (-(1 : ℝ)) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ C * (2 * ∫ u in (0 : ℝ)..(T : ℝ), (1 + |u|) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_left (c12_power_kernel_interval_bound 1 (T : ℝ) s hs.1 hs.2) hC
      _ = _ := by rw [hk]; ring
  have hd : (∫ s in (0 : ℝ)..(T : ℝ), ∫ u in (0 : ℝ)..(T : ℝ), q s u) ≤
      (T : ℝ) * (2*C*Real.log (1+(T : ℝ))) := by
    calc
      _ ≤ ∫ _s in (0 : ℝ)..(T : ℝ), 2*C*Real.log (1+(T : ℝ)) :=
        intervalIntegral.integral_mono_on T.coe_nonneg hint.2 intervalIntegrable_const hinner
      _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  have hlog : 0 ≤ Real.log (1+(T : ℝ)) := Real.log_nonneg (by linarith)
  rw [c12_physical_clock_l2_eq_double_correlation μ η T hTnn]
  change (T : ℝ)⁻¹^2 * (∫ s in (0 : ℝ)..(T : ℝ), ∫ u in (0 : ℝ)..(T : ℝ), q s u) ≤ _
  calc
    _ ≤ (T : ℝ)⁻¹^2 * ((T : ℝ) * (2*C*Real.log (1+(T : ℝ)))) :=
      mul_le_mul_of_nonneg_left hd (sq_nonneg _)
    _ = (2*C)*Real.log (1+(T : ℝ))/(T : ℝ) := by
      have htne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
      field_simp
      <;> ring
    _ ≤ (4*C)*Real.log (1+(T : ℝ))/(T : ℝ) := by
      apply (div_le_div_iff_of_pos_right hTpos).2
      nlinarith

/-- Summable power correlation decay yields an inverse-time clock variance bound. -/
theorem c12_physical_clock_l2_inverse_time_bound_of_summable_correlation_decay {d : ℕ} {L : ℝ}
 (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
 (η C α : ℝ) (hC : 0 ≤ C) (hα : 1 < α)
 (hcorr : ∀ s u : ℝ≥0,
  |∫ z : ReductionImageV3.PhysicalField d L × Path d,
   (Real.exp (-2*z.1.1.2 (z.2 s))-η)*
   (Real.exp (-2*z.1.1.2 (z.2 u))-η) ∂μ| ≤
   C*Real.rpow (1+|(s : ℝ)-(u : ℝ)|) (-α)) :
 ∀ T : ℝ≥0, 1 ≤ (T : ℝ) →
 (∫ z : ReductionImageV3.PhysicalField d L × Path d,
  ((Clock.physicalPathClock z.1.1 z.2 T : ℝ)/(T : ℝ)-η)^2 ∂μ) ≤
  (2*C/(α-1))/(T : ℝ) := by
  intro T hT
  let Z := ReductionImageV3.PhysicalField d L × Path d
  let q : ℝ → ℝ → ℝ := fun s u => ∫ z : Z,
    (Real.exp (-2*z.1.1.2 (z.2 s.toNNReal))-η)*
    (Real.exp (-2*z.1.1.2 (z.2 u.toNNReal))-η) ∂μ
  have hTpos : 0 < (T : ℝ) := by linarith
  have hTnn : (0 : ℝ≥0) < T := by exact_mod_cast hTpos
  have hint := c12_clock_correlation_interval_integrable μ η T
  have hk : (∫ u in (0 : ℝ)..(T : ℝ), (1 + |u|) ^ (-α)) ≤ 1 / (α - 1) := by
    have heq : (∫ u in (0 : ℝ)..(T : ℝ), (1 + |u|) ^ (-α)) =
        ∫ u in (1 : ℝ)..(1 + (T : ℝ)), u ^ (-α) := by
      calc
        _ = ∫ u in (0 : ℝ)..(T : ℝ), (1 + u) ^ (-α) := by
          apply intervalIntegral.integral_congr
          intro u hu
          dsimp only
          rw [abs_of_nonneg ((Set.uIcc_of_le T.coe_nonneg ▸ hu).1)]
        _ = _ := by
          simpa only [add_zero] using
            (intervalIntegral.integral_comp_add_left (fun u : ℝ => u ^ (-α)) (a := 0) (b := (T : ℝ)) 1)
    rw [heq, integral_rpow (Or.inr ⟨by linarith, by
      rw [Set.uIcc_of_le (by linarith : (1 : ℝ) ≤ 1 + (T : ℝ))]
      simp⟩), Real.one_rpow]
    have hp : 0 ≤ (1 + (T : ℝ)) ^ (-α + 1) := Real.rpow_nonneg (by positivity) _
    have hden : 0 < α - 1 := by linarith
    have he : -α + 1 = -(α - 1) := by ring
    rw [he] at hp
    rw [he, div_neg]
    rw [← neg_div]
    apply (div_le_div_iff_of_pos_right hden).2
    linarith
  have hinner : ∀ s ∈ Set.Icc (0 : ℝ) (T : ℝ),
      (∫ u in (0 : ℝ)..(T : ℝ), q s u) ≤ 2*C/(α-1) := by
    intro s hs
    have hc : Continuous (fun u : ℝ => C * (1 + |s-u|) ^ (-α)) := by
      apply continuous_const.mul
      apply (continuous_const.add (continuous_const.sub continuous_id).abs).rpow_const
      intro x
      left
      have : 0 < 1 + |s-x| := by positivity
      exact ne_of_gt this
    calc
      _ ≤ ∫ u in (0 : ℝ)..(T : ℝ), C * (1 + |s-u|) ^ (-α) := by
        apply intervalIntegral.integral_mono_on T.coe_nonneg (hint.1 s) (hc.intervalIntegrable _ _)
        intro u hu
        have h := hcorr s.toNNReal u.toNNReal
        rw [Real.coe_toNNReal _ hs.1, Real.coe_toNNReal _ hu.1] at h
        exact le_trans (le_abs_self _) h
      _ = C * ∫ u in (0 : ℝ)..(T : ℝ), (1 + |s-u|) ^ (-α) := by
        rw [intervalIntegral.integral_const_mul]
      _ ≤ C * (2 * ∫ u in (0 : ℝ)..(T : ℝ), (1 + |u|) ^ (-α)) :=
        mul_le_mul_of_nonneg_left (c12_power_kernel_interval_bound α (T : ℝ) s hs.1 hs.2) hC
      _ ≤ 2*C/(α-1) := by
        have hh := mul_le_mul_of_nonneg_left hk (show 0 ≤ 2*C by positivity)
        convert hh using 1 <;> ring
  have hd : (∫ s in (0 : ℝ)..(T : ℝ), ∫ u in (0 : ℝ)..(T : ℝ), q s u) ≤
      (T : ℝ) * (2*C/(α-1)) := by
    calc
      _ ≤ ∫ _s in (0 : ℝ)..(T : ℝ), 2*C/(α-1) :=
        intervalIntegral.integral_mono_on T.coe_nonneg hint.2 intervalIntegrable_const hinner
      _ = _ := by simp only [intervalIntegral.integral_const, sub_zero, smul_eq_mul]
  rw [c12_physical_clock_l2_eq_double_correlation μ η T hTnn]
  change (T : ℝ)⁻¹^2 * (∫ s in (0 : ℝ)..(T : ℝ), ∫ u in (0 : ℝ)..(T : ℝ), q s u) ≤ _
  calc
    _ ≤ (T : ℝ)⁻¹^2 * ((T : ℝ) * (2*C/(α-1))) :=
      mul_le_mul_of_nonneg_left hd (sq_nonneg _)
    _ = _ := by
      have htne : (T : ℝ) ≠ 0 := ne_of_gt hTpos
      field_simp
      <;> ring

/-- Square-time convergence of a physical clock extends to all nonnegative times. -/
theorem c12_clock_speed_of_square_time {d : ℕ} (ω : FieldPair d) (γ : Path d) (η : ℝ)
    (h : Tendsto (fun n : ℕ =>
      (Clock.physicalPathClock ω γ (((n + 1)^2 : ℕ) : ℝ≥0) : ℝ) /
        (((n + 1)^2 : ℕ) : ℝ)) atTop (𝓝 η)) :
    Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η := by
  let u : ℕ → ℝ := fun n => (Clock.physicalPathClock ω γ (n : ℝ≥0) : ℝ)
  have hm : Monotone u := by
    intro a b hab
    exact Clock.physicalPathClock_mono (ω, γ) (by exact_mod_cast hab)
  have hn : Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop (𝓝 η) := by
    apply tendsto_div_of_monotone_of_exists_subseq_tendsto_div u η hm
    intro a ha
    refine ⟨fun n => (n + 1)^2, ?_, ?_, h⟩
    · have hr : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1))^2)
          atTop (𝓝 1) := by
        simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).pow 2
      have he := (tendsto_order.1 hr).2 a ha
      filter_upwards [he] with n hn
      have hp : 0 < (n : ℝ) + 1 := by positivity
      have hb := (div_lt_iff₀ (sq_pos_of_pos hp)).mp (by
        convert hn using 1 <;> field_simp <;> ring :
          (((n : ℝ) + 2)^2) / (((n : ℝ) + 1)^2) < a)
      push_cast
      nlinarith only [hb]
    · apply tendsto_atTop_mono' atTop ?_ (tendsto_add_atTop_nat 1)
      exact Filter.Eventually.of_forall (fun n : ℕ => le_self_pow (show 1 ≤ n + 1 by omega) (show (2 : ℕ) ≠ 0 by omega))
  exact Clock.tendsto_div_of_tendsto_natCast
    (fun t => NNReal.coe_nonneg (Clock.physicalPathClock ω γ t))
    (fun _ _ hst => Clock.physicalPathClock_mono (ω, γ) hst) hn

/-- Summable second moments imply almost-sure convergence of the errors. -/
theorem c12_ae_tendsto_zero_of_summable_square_integrals
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (f : ℕ → Ω → ℝ)
    (hi : ∀ n, Integrable (fun z => (f n z)^2) μ)
    (hs : Summable (fun n => ∫ z, (f n z)^2 ∂μ)) :
    ∀ᵐ z ∂μ, Tendsto (fun n => f n z) atTop (𝓝 0) := by
  let g : ℕ → Ω → ℝ := fun n z => (f n z)^2
  have hg : (∑' n, eLpNorm (g n) 1 μ) ≠ ∞ := by
    have heq (n : ℕ) : eLpNorm (g n) 1 μ = ENNReal.ofReal (∫ z, g n z ∂μ) := by
      rw [eLpNorm_one_eq_lintegral_enorm (hi n).aestronglyMeasurable]
      rw [ofReal_integral_eq_lintegral_ofReal (hi n) (Filter.Eventually.of_forall
        (fun z => sq_nonneg (f n z)))]
      apply lintegral_congr
      intro z
      exact Real.enorm_eq_ofReal (sq_nonneg (f n z))
    simp_rw [heq]
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun n => integral_nonneg (fun z => sq_nonneg (f n z))) hs]
    exact ENNReal.ofReal_ne_top
  filter_upwards [summable_norm_of_tsum_eLpNorm_ne_top (by norm_num : (1 : ℝ≥0∞) ≤ 1) hg]
    with z hz
  have ht := hz.tendsto_atTop_zero
  have ht' : Tendsto (fun n => (f n z)^2) atTop (𝓝 0) := by
    simpa only [g, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f _ z))] using ht
  have ha := Real.continuous_sqrt.continuousAt.tendsto.comp ht'
  apply (tendsto_zero_iff_abs_tendsto_zero _).2
  simpa only [Real.sqrt_sq_eq_abs, Real.sqrt_zero, Real.norm_eq_abs, Function.comp_def] using ha

/-- Summable correlation decay yields the almost-sure physical clock speed. -/
theorem c12_physical_clock_speed_ae_of_summable_correlation_decay
 {d : ℕ} {L : ℝ}
 (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
 (η C α : ℝ) (hC : 0 ≤ C) (hα : 1 < α)
 (hcorr : ∀ s u : ℝ≥0,
  |∫ z : ReductionImageV3.PhysicalField d L × Path d,
   (Real.exp (-2*z.1.1.2 (z.2 s))-η)*
   (Real.exp (-2*z.1.1.2 (z.2 u))-η) ∂μ| ≤
   C*Real.rpow (1+|(s : ℝ)-(u : ℝ)|) (-α)) :
 ∀ᵐ z ∂μ, Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed z.1.1 z.2 η := by
  let Z := ReductionImageV3.PhysicalField d L × Path d
  let t : ℕ → ℝ≥0 := fun n => (((n + 1)^2 : ℕ) : ℝ≥0)
  let f : ℕ → Z → ℝ := fun n z =>
    (Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ) / (t n : ℝ) - η
  have ht (n : ℕ) : 1 ≤ (t n : ℝ) := by
    dsimp [t]
    push_cast
    nlinarith [sq_nonneg (n : ℝ), Nat.cast_nonneg (α := ℝ) n]
  have hi (n : ℕ) : Integrable (fun z => (f n z)^2) μ := by
    have hc : Continuous (fun z : Z => (Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ)) :=
      (Clock.continuous_physicalPathClock_at (d := d) (t n)).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    have hf : Continuous (f n) := (hc.div_const _).sub continuous_const
    apply Integrable.of_bound (hf.pow 2).aestronglyMeasurable ((Real.exp (2*L)+|η|)^2)
    filter_upwards with z
    have hclock := (Clock.InverseMeaningV3.physicalPathClock_bounds z.1.1 z.2 L
      z.1.2.2.1 (t n)).2
    have hpos : 0 < (t n : ℝ) := lt_of_lt_of_le zero_lt_one (ht n)
    have hratio : 0 ≤ (Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ) / (t n : ℝ) ∧
      (Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ) / (t n : ℝ) ≤ Real.exp (2*L) :=
      ⟨div_nonneg (NNReal.coe_nonneg _) hpos.le, (div_le_iff₀ hpos).2 hclock⟩
    have habs : |f n z| ≤ Real.exp (2*L)+|η| := by
      dsimp [f]
      calc
        _ ≤ |(Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ) / (t n : ℝ)| + |η| := abs_sub _ _
        _ ≤ _ := by rw [abs_of_nonneg hratio.1]; linarith only [hratio.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (f n z)^2 ≤ _
    rw [← sq_abs (f n z)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hs : Summable (fun n => ∫ z, (f n z)^2 ∂μ) := by
    have hp : Summable (fun n : ℕ => (2*C/(α-1)) / (((n+1 : ℕ) : ℝ)^2)) := by
      have h := (Real.summable_one_div_nat_pow.mpr (by norm_num : 1 < (2 : ℕ))).comp_injective
        (Nat.succ_injective)
      simpa only [Function.comp_def, Nat.cast_succ, Nat.cast_add, Nat.cast_one, one_mul, div_eq_mul_inv] using h.mul_left (2*C/(α-1))
    apply hp.of_nonneg_of_le
    · intro n
      exact integral_nonneg (fun z => sq_nonneg _)
    · intro n
      have h := c12_physical_clock_l2_inverse_time_bound_of_summable_correlation_decay
        μ η C α hC hα hcorr (t n) (ht n)
      simpa only [f, t, Nat.cast_pow, NNReal.coe_natCast, NNReal.coe_pow] using h
  filter_upwards [c12_ae_tendsto_zero_of_summable_square_integrals μ f hi hs] with z hz
  apply c12_clock_speed_of_square_time z.1.1 z.2 η
  have h := hz.add_const η
  simpa only [f, t, sub_add_cancel, zero_add, NNReal.coe_natCast] using h

/-- Polynomial-time convergence of a physical clock extends to all times. -/
theorem c12_clock_speed_of_polynomial_time {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (η : ℝ) (p : ℕ) (hp : p ≠ 0)
    (h : Tendsto (fun n : ℕ =>
      (Clock.physicalPathClock ω γ (((n + 1)^p : ℕ) : ℝ≥0) : ℝ) /
        (((n + 1)^p : ℕ) : ℝ)) atTop (𝓝 η)) :
    Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η := by
  let u : ℕ → ℝ := fun n => (Clock.physicalPathClock ω γ (n : ℝ≥0) : ℝ)
  have hm : Monotone u := by
    intro a b hab
    exact Clock.physicalPathClock_mono (ω, γ) (by exact_mod_cast hab)
  have hn : Tendsto (fun n : ℕ => u n / (n : ℝ)) atTop (𝓝 η) := by
    apply tendsto_div_of_monotone_of_exists_subseq_tendsto_div u η hm
    intro a ha
    refine ⟨fun n => (n + 1)^p, ?_, ?_, h⟩
    · have hr : Tendsto (fun n : ℕ => (1 + 1 / ((n : ℝ) + 1))^p)
          atTop (𝓝 1) := by
        simpa using ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
          (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))).pow p
      have he := (tendsto_order.1 hr).2 a ha
      filter_upwards [he] with n hn
      have hnpos : 0 < (n : ℝ) + 1 := by positivity
      have heq : ((n : ℝ) + 2)^p / ((n : ℝ) + 1)^p =
          (1 + 1 / ((n : ℝ) + 1))^p := by
        rw [← div_pow]
        congr 1
        field_simp
        <;> ring
      have hb := (div_lt_iff₀ (pow_pos hnpos p)).mp (heq ▸ hn)
      push_cast
      simpa only [Nat.cast_add, Nat.cast_one, add_assoc, show (1 : ℝ) + 1 = 2 by norm_num] using hb.le
    · apply tendsto_atTop_mono' atTop ?_ (tendsto_add_atTop_nat 1)
      exact Filter.Eventually.of_forall (fun n : ℕ => le_self_pow (show 1 ≤ n + 1 by omega) hp)
  exact Clock.tendsto_div_of_tendsto_natCast
    (fun t => NNReal.coe_nonneg (Clock.physicalPathClock ω γ t))
    (fun _ _ hst => Clock.physicalPathClock_mono (ω, γ) hst) hn

/-- Any positive polynomial correlation decay yields almost-sure clock speed. -/
theorem c12_physical_clock_speed_ae_of_polynomial_correlation_decay
 {d : ℕ} {L : ℝ}
 (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
 (η C α : ℝ) (hC : 0 ≤ C) (hα : 0 < α)
 (hcorr : ∀ s u : ℝ≥0,
  |∫ z : ReductionImageV3.PhysicalField d L × Path d,
   (Real.exp (-2*z.1.1.2 (z.2 s))-η)*
   (Real.exp (-2*z.1.1.2 (z.2 u))-η) ∂μ| ≤
   C*Real.rpow (1+|(s : ℝ)-(u : ℝ)|) (-α)) :
 ∀ᵐ z ∂μ, Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed z.1.1 z.2 η := by
  let β : ℝ := min α 1 / 2
  have hβ : 0 < β := by dsimp [β]; positivity
  have hβ1 : β < 1 := by dsimp [β]; have := min_le_right α (1 : ℝ); linarith
  have hβα : β ≤ α := by dsimp [β]; have := min_le_left α (1 : ℝ); linarith
  have hcorrβ : ∀ s u : ℝ≥0,
    |∫ z : ReductionImageV3.PhysicalField d L × Path d,
      (Real.exp (-2*z.1.1.2 (z.2 s))-η)*
      (Real.exp (-2*z.1.1.2 (z.2 u))-η) ∂μ| ≤
      C * Real.rpow (1+|(s : ℝ)-(u : ℝ)|) (-β) := by
    intro s u
    exact (hcorr s u).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by linarith [abs_nonneg ((s : ℝ)-(u : ℝ))])
        (by linarith)) hC)
  obtain ⟨p, hp⟩ := exists_nat_gt (1 / β)
  have hpβ : 1 < (p : ℝ) * β := (div_lt_iff₀ hβ).mp hp
  have hp0 : p ≠ 0 := by intro h; simp [h] at hpβ; linarith
  let Z := ReductionImageV3.PhysicalField d L × Path d
  let t : ℕ → ℝ≥0 := fun n => (((n + 1)^p : ℕ) : ℝ≥0)
  let f : ℕ → Z → ℝ := fun n z =>
    (Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ) / (t n : ℝ) - η
  have ht (n : ℕ) : 1 ≤ (t n : ℝ) := by
    dsimp [t]
    exact_mod_cast (show 1 ≤ (n + 1)^p from one_le_pow₀ (by omega))
  have hi (n : ℕ) : Integrable (fun z => (f n z)^2) μ := by
    have hc : Continuous (fun z : Z => (Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ)) :=
      (Clock.continuous_physicalPathClock_at (d := d) (t n)).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    have hf : Continuous (f n) := (hc.div_const _).sub continuous_const
    apply Integrable.of_bound (hf.pow 2).aestronglyMeasurable ((Real.exp (2*L)+|η|)^2)
    filter_upwards with z
    have hclock := (Clock.InverseMeaningV3.physicalPathClock_bounds z.1.1 z.2 L
      z.1.2.2.1 (t n)).2
    have hpos : 0 < (t n : ℝ) := lt_of_lt_of_le zero_lt_one (ht n)
    have hratio : 0 ≤ (Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ) / (t n : ℝ) ∧
      (Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ) / (t n : ℝ) ≤ Real.exp (2*L) :=
      ⟨div_nonneg (NNReal.coe_nonneg _) hpos.le, (div_le_iff₀ hpos).2 hclock⟩
    have habs : |f n z| ≤ Real.exp (2*L)+|η| := by
      dsimp [f]
      calc
        _ ≤ |(Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ) / (t n : ℝ)| + |η| := abs_sub _ _
        _ ≤ _ := by rw [abs_of_nonneg hratio.1]; linarith only [hratio.2]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    change (f n z)^2 ≤ _
    rw [← sq_abs (f n z)]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hs : Summable (fun n => ∫ z, (f n z)^2 ∂μ) := by
    have hpseries : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) ^ (-(p : ℝ)*β)) := by
      have h := (Real.summable_nat_rpow.mpr (by linarith : -(p : ℝ)*β < -1)).comp_injective Nat.succ_injective
      simpa only [Function.comp_def] using h
    have hs' := hpseries.mul_left (4*C/(1-β))
    apply hs'.of_nonneg_of_le
    · intro n
      exact integral_nonneg (fun z => sq_nonneg _)
    · intro n
      have h := c12_physical_clock_l2_power_bound_of_correlation_decay
        μ η C β hC hβ hβ1 hcorrβ (t n) (ht n)
      have heq : Real.rpow (t n : ℝ) (-β) = ((n + 1 : ℕ) : ℝ) ^ (-(p : ℝ)*β) := by
        dsimp [t]
        rw [NNReal.coe_natCast, Nat.cast_pow, ← Real.rpow_natCast,
          ← Real.rpow_mul (by positivity)]
        congr 1 <;> ring
      rw [heq] at h
      exact h
  filter_upwards [c12_ae_tendsto_zero_of_summable_square_integrals μ f hi hs] with z hz
  apply c12_clock_speed_of_polynomial_time z.1.1 z.2 η p hp0
  have h := hz.add_const η
  simpa only [f, t, sub_add_cancel, zero_add, NNReal.coe_natCast] using h

/-- Polynomial correlation decay also determines the speed of the actual inverse clock. -/
theorem c12_inverse_clock_speed_ae_of_polynomial_correlation_decay
 {d : ℕ} {L : ℝ}
 (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
 (η C α : ℝ) (hC : 0 ≤ C) (hα : 0 < α)
 (hcorr : ∀ s u : ℝ≥0,
  |∫ z : ReductionImageV3.PhysicalField d L × Path d,
   (Real.exp (-2*z.1.1.2 (z.2 s))-η)*
   (Real.exp (-2*z.1.1.2 (z.2 u))-η) ∂μ| ≤
   C*Real.rpow (1+|(s : ℝ)-(u : ℝ)|) (-α)) :
 (Real.exp (-2*L) ≤ η ∧ η ≤ Real.exp (2*L)) ∧
 ∀ᵐ z ∂μ, ∀ hω : IsRegular L z.1.1,
  Clock.PhysicalClockSpeedMeaningV5.HasInverseClockSpeed z.1.1 z.2 L η⁻¹ hω := by
  have hae := c12_physical_clock_speed_ae_of_polynomial_correlation_decay μ η C α hC hα hcorr
  obtain ⟨z, hz⟩ := hae.exists
  have hb : ∀ᶠ t : ℝ≥0 in atTop,
      Real.exp (-2*L) ≤ (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) ∧
      (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) ≤ Real.exp (2*L) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have h := Clock.InverseMeaningV3.physicalPathClock_bounds z.1.1 z.2 L z.1.2.2.1 t
    exact ⟨(le_div_iff₀ ht').2 h.1, (div_le_iff₀ ht').2 h.2⟩
  refine ⟨⟨le_of_tendsto_of_tendsto tendsto_const_nhds hz (hb.mono fun _ h => h.1),
    le_of_tendsto_of_tendsto hz tendsto_const_nhds (hb.mono fun _ h => h.2)⟩, ?_⟩
  filter_upwards [hae] with z hz hω
  exact Clock.PhysicalClockSpeedMeaningV5.hasClockSpeed_to_hasInverseClockSpeed
    z.1.1 z.2 L η hω hz

/-- An almost-sure clock speed equals the common mean of the actual clock density. -/
theorem c12_physical_clock_speed_eq_density_mean
 {d : ℕ} {L : ℝ}
 (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
 (η mean : ℝ)
 (hspeed : ∀ᵐ z ∂μ, Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed z.1.1 z.2 η)
 (hmean : ∀ s : ℝ≥0, (∫ z : ReductionImageV3.PhysicalField d L × Path d,
   Real.exp (-2*z.1.1.2 (z.2 s)) ∂μ) = mean) :
 η = mean := by
  let Z := ReductionImageV3.PhysicalField d L × Path d
  let f : Z → ℝ → ℝ := fun z s => Real.exp (-2*z.1.1.2 (z.2 s.toNNReal))-mean
  let K : ℝ := Real.exp (2 * L) + |mean|
  have hf : Continuous (fun p : ℝ × Z => f p.2 p.1) := by
    have hc := Clock.continuous_clockDensity_time_path (d := d)
    exact (hc.comp (continuous_fst.prodMk
      ((continuous_subtype_val.comp continuous_snd.fst).prodMk continuous_snd.snd))).sub
      continuous_const
  have hb : ∀ z s, ‖f z s‖ ≤ K := by
    intro z s
    simpa only [Real.norm_eq_abs] using c12_centered_clock_density_bound z mean s
  have hint (T : ℝ≥0) (hT : 0 < T) :
      (∫ z : Z, ((Clock.physicalPathClock z.1.1 z.2 T : ℝ) / (T : ℝ) - mean) ∂μ) = 0 := by
    have hfin : (volume : Measure ℝ) (Set.uIoc (0 : ℝ) (T : ℝ)) ≠ ⊤ := by
      rw [Set.uIoc_of_le T.coe_nonneg, Real.volume_Ioc]
      exact ENNReal.ofReal_ne_top
    let ν := (volume : Measure ℝ).restrict (Set.uIoc (0 : ℝ) (T : ℝ))
    haveI : IsFiniteMeasure ν := isFiniteMeasure_restrict.mpr hfin
    have hprod : Integrable (fun p : ℝ × Z => f p.2 p.1) (ν.prod μ) := by
      apply Integrable.of_bound hf.aestronglyMeasurable K
      filter_upwards with p
      exact hb p.2 p.1
    calc
      _ = (T : ℝ)⁻¹ * ∫ z : Z, (∫ s in (0 : ℝ)..(T : ℝ), f z s) ∂μ := by
        rw [← integral_const_mul]
        apply integral_congr_ae
        filter_upwards with z
        exact c12_physical_clock_centered_integral z mean T hT
      _ = (T : ℝ)⁻¹ * ∫ s in (0 : ℝ)..(T : ℝ), ∫ z : Z, f z s ∂μ := by
        rw [intervalIntegral_integral_swap hprod]
      _ = 0 := by
        have hz (s : ℝ) : (∫ z : Z, f z s ∂μ) = 0 := by
          have hs : Integrable (fun z : Z => Real.exp (-2*z.1.1.2 (z.2 s.toNNReal))) μ := by
            have hc : Continuous (fun z : Z => Real.exp (-2*z.1.1.2 (z.2 s.toNNReal))) := by
              have hc := (hf.comp ((continuous_const : Continuous (fun _ : Z => s)).prodMk continuous_id)).add (continuous_const : Continuous (fun _ : Z => mean))
              convert hc using 1
              funext z
              simp [f]
            apply Integrable.of_bound hc.aestronglyMeasurable (Real.exp (2*L))
            filter_upwards with z
            rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
            exact (clockDensity_bounds z.1.1 (z.2 s.toNNReal) L (z.1.2.2.1 _)).2
          simp only [f, integral_sub hs (integrable_const mean), integral_const, smul_eq_mul,
            probReal_univ, one_mul]
          exact sub_eq_zero.mpr (hmean s.toNNReal)
        simp only [hz, intervalIntegral.integral_zero, mul_zero]
  let t : ℕ → ℝ≥0 := fun n => ((n + 1 : ℕ) : ℝ≥0)
  let F : ℕ → Z → ℝ := fun n z =>
    (Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ) / (t n : ℝ) - mean
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n) μ := by
    have hc : Continuous (fun z : Z => (Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ)) :=
      (Clock.continuous_physicalPathClock_at (d := d) (t n)).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    exact ((hc.div_const _).sub continuous_const).aestronglyMeasurable
  have hbound (n : ℕ) : ∀ᵐ z ∂μ, ‖F n z‖ ≤ K := by
    filter_upwards with z
    have ht : 0 < (t n : ℝ) := by dsimp [t]; positivity
    have hclock := (Clock.InverseMeaningV3.physicalPathClock_bounds z.1.1 z.2 L
      z.1.2.2.1 (t n)).2
    have hratio : 0 ≤ (Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ) / (t n : ℝ) ∧
      (Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ) / (t n : ℝ) ≤ Real.exp (2*L) :=
      ⟨div_nonneg (NNReal.coe_nonneg _) ht.le, (div_le_iff₀ ht).2 hclock⟩
    rw [Real.norm_eq_abs]
    calc
      _ ≤ |(Clock.physicalPathClock z.1.1 z.2 (t n) : ℝ) / (t n : ℝ)| + |mean| := abs_sub _ _
      _ ≤ K := by
        rw [abs_of_nonneg hratio.1]
        change _ ≤ Real.exp (2 * L) + |mean|
        linarith only [hratio.2]
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun n => F n z) atTop (𝓝 (η - mean)) := by
    filter_upwards [hspeed] with z hz
    have ht : Tendsto t atTop atTop := by
      exact tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    exact (hz.comp ht).sub_const mean
  have hd := tendsto_integral_of_dominated_convergence (fun _ : Z => K) hmeas
    (integrable_const K) hbound hlim
  have heq : (fun n => ∫ z : Z, F n z ∂μ) = fun _ => (0 : ℝ) := by
    funext n
    exact hint (t n) (by dsimp [t]; positivity)
  rw [heq] at hd
  have hh : (0 : ℝ) = η - mean := by
    apply tendsto_nhds_unique (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))
    simpa only [integral_const, probReal_univ, one_smul] using hd
  linarith


/-- Almost-sure speed of the physical clock implies convergence of its second moment. -/
theorem c12_physical_clock_l2_tendsto_zero_of_ae_clock_speed
 {d : ℕ} {L : ℝ}
 (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
 (η : ℝ)
 (hspeed : ∀ᵐ z ∂μ, Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed z.1.1 z.2 η) :
 Tendsto (fun t : ℝ≥0 => ∫ z : ReductionImageV3.PhysicalField d L × Path d,
  ((Clock.physicalPathClock z.1.1 z.2 t : ℝ)/(t : ℝ)-η)^2 ∂μ)
  atTop (𝓝 0) := by
  let Z := ReductionImageV3.PhysicalField d L × Path d
  let F : ℝ≥0 → Z → ℝ := fun t z =>
    ((Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η)^2
  let K : ℝ := Real.exp (2 * L) + |η|
  have hK : 0 ≤ K := add_nonneg (Real.exp_pos _).le (abs_nonneg _)
  have hmeas : ∀ᶠ t : ℝ≥0 in atTop, AEStronglyMeasurable (F t) μ := by
    filter_upwards with t
    have hc : Continuous (fun z : Z => (Clock.physicalPathClock z.1.1 z.2 t : ℝ)) :=
      (Clock.continuous_physicalPathClock_at (d := d) t).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    exact (((hc.div_const _).sub continuous_const).pow 2).aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ≥0 in atTop, ∀ᵐ z ∂μ, ‖F t z‖ ≤ K^2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    filter_upwards with z
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have hclock := (Clock.InverseMeaningV3.physicalPathClock_bounds z.1.1 z.2 L
      z.1.2.2.1 t).2
    have hratio : 0 ≤ (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) ∧
      (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) ≤ Real.exp (2*L) :=
      ⟨div_nonneg (NNReal.coe_nonneg _) ht'.le, (div_le_iff₀ ht').2 hclock⟩
    have habs : |(Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η| ≤ K := by
      calc
        _ ≤ |(Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ)| + |η| := abs_sub _ _
        _ ≤ K := by
          rw [abs_of_nonneg hratio.1]
          change _ ≤ Real.exp (2 * L) + |η|
          exact add_le_add hratio.2 le_rfl
    change |((Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η)^2| ≤ K^2
    rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 2
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun t => F t z) atTop (𝓝 0) := by
    filter_upwards [hspeed] with z hz
    simpa [F] using (hz.sub_const η).pow 2
  have hd := tendsto_integral_filter_of_dominated_convergence (fun _ : Z => K^2)
    hmeas hbound (integrable_const _) hlim
  simpa only [F, integral_zero] using hd

/-- Almost-sure speed of the physical clock implies convergence of its fourth error moment. -/
theorem c12_physical_clock_fourth_error_tendsto_zero_of_ae_clock_speed
 {d : ℕ} {L : ℝ}
 (μ : Measure (ReductionImageV3.PhysicalField d L × Path d)) [IsProbabilityMeasure μ]
 (η : ℝ)
 (hspeed : ∀ᵐ z ∂μ, Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed z.1.1 z.2 η) :
 Tendsto (fun t : ℝ≥0 => ∫ z : ReductionImageV3.PhysicalField d L × Path d,
  ((Clock.physicalPathClock z.1.1 z.2 t : ℝ)/(t : ℝ)-η)^4 ∂μ)
  atTop (𝓝 0) := by
  let Z := ReductionImageV3.PhysicalField d L × Path d
  let F : ℝ≥0 → Z → ℝ := fun t z =>
    ((Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η)^4
  let K : ℝ := Real.exp (2 * L) + |η|
  have hmeas : ∀ᶠ t : ℝ≥0 in atTop, AEStronglyMeasurable (F t) μ := by
    filter_upwards with t
    have hc : Continuous (fun z : Z => (Clock.physicalPathClock z.1.1 z.2 t : ℝ)) :=
      (Clock.continuous_physicalPathClock_at (d := d) t).comp
        ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)
    exact (((hc.div_const _).sub continuous_const).pow 4).aestronglyMeasurable
  have hbound : ∀ᶠ t : ℝ≥0 in atTop, ∀ᵐ z ∂μ, ‖F t z‖ ≤ K^4 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    filter_upwards with z
    have ht' : (0 : ℝ) < t := by exact_mod_cast ht
    have hclock := (Clock.InverseMeaningV3.physicalPathClock_bounds z.1.1 z.2 L
      z.1.2.2.1 t).2
    have hratio : 0 ≤ (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) ∧
      (Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) ≤ Real.exp (2*L) :=
      ⟨div_nonneg (NNReal.coe_nonneg _) ht'.le, (div_le_iff₀ ht').2 hclock⟩
    have habs : |(Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η| ≤ K := by
      calc
        _ ≤ |(Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ)| + |η| := abs_sub _ _
        _ ≤ K := by
          rw [abs_of_nonneg hratio.1]
          change _ ≤ Real.exp (2 * L) + |η|
          exact add_le_add hratio.2 le_rfl
    change |((Clock.physicalPathClock z.1.1 z.2 t : ℝ) / (t : ℝ) - η)^4| ≤ K^4
    rw [abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) habs 4
  have hlim : ∀ᵐ z ∂μ, Tendsto (fun t => F t z) atTop (𝓝 0) := by
    filter_upwards [hspeed] with z hz
    simpa [F] using (hz.sub_const η).pow 4
  have hd := tendsto_integral_filter_of_dominated_convergence (fun _ : Z => K^4)
    hmeas hbound (integrable_const _) hlim
  simpa only [F, integral_zero] using hd

/-- The proved reduced-law foundation supplies the sharp clock graph reduction. -/
theorem sharp_clock_reduction_from_proved_foundation
    (_h0 : node_app_u3A_sharp_u2D_harmonicStmt)
    (_h1 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h2 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2) :
    node_app_u3A_sharp_u2D_clockStmt :=
  sharp_clock_of_announced_reduced_foundation EinsteinFull.c16_reduced_mp_exists _h0 _h1 h2

/-- Assemble the sharp clock from the shared fields and time-change inputs. -/
theorem sharp_clock_from_fields_and_time_change
    (hfields : node_app_u3A_sharp_u2D_fieldsStmt)
    (htime : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2) :
    node_app_u3A_sharp_u2D_clockStmt :=
  sharp_clock_reduction_from_proved_foundation
    (sharp_harmonic_reduction_from_proved_foundation hfields htime) hfields htime

open EinsteinRelation.Sharpness

/-- The actual clock rate has a linear bound in the signed force. -/
theorem sharp_actual_clock_rate_linear_force_bound_from_graph
    (h0 : node_app_u3A_sharp_u2D_harmonicStmt)
    (h1 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h2 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω))) :
    ∃ η avg : ℝ, HasReducedClockRate Q Y η ∧
      η = 1 - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * lam * (avg-1) ∧
      |avg| ≤ 3 ∧ |η-1| ≤
        4 * EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * |lam| := by
  let i : Fin d := ⟨0, by omega⟩
  obtain ⟨_, hclock⟩ := sharp_clock_reduction_from_proved_foundation h0 h1 h2 d hd P hP D Q hQ
  obtain ⟨η, avg, hrate, heq, havg, _⟩ := hclock lam hlam Y hY
  have hpull : ∀ᵐ W ∂P,
      (∀ᵐ γ ∂originLaw Y (EinsteinFull.Work.W8.physicalPair i W),
        Tendsto (fun t : ℝ => t⁻¹ * ∫ u in (0 : ℝ)..t,
          reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) (γ u.toNNReal) i i)
          atTop (𝓝 avg)) ∧
      SolvesMartingaleProblem (reducedGenerator i (EinsteinFull.Work.W8.physicalPair i W) lam)
        0 (Y (0, EinsteinFull.Work.W8.physicalPair i W)) := by
    have h := havg.and hY
    rw [hQ] at h
    exact ae_of_ae_map (EinsteinFull.Work.W8.measurable_physicalPair i).aemeasurable h
  let _ : IsProbabilityMeasure P := hP.1
  obtain ⟨W, hW, hmp⟩ := hpull.exists
  let _ : IsProbabilityMeasure (originLaw Y (EinsteinFull.Work.W8.physicalPair i W)) := hmp.1
  obtain ⟨γ, hγ⟩ := hW.exists
  have hb : ∀ x, 0 ≤ reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x i i ∧
      reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x i i ≤ 3 := by
    intro x
    have h := (EinsteinFull.Work.W8.reducedCoefficient_isElliptic i W x).2 (unitVector i)
    have hs : euclideanSq (unitVector i) = 1 := by simp [euclideanSq, dot, unitVector, Pi.single_apply]
    have hdg : dot (unitVector i) ((reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x).mulVec (unitVector i)) =
        reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) x i i := by
      simp [dot, unitVector, Pi.single_apply]
    rw [hs, hdg] at h
    norm_num at h
    constructor <;> linarith [h.1, h.2]
  have htbound : ∀ t : ℝ, 0 < t →
      0 ≤ t⁻¹ * ∫ u in (0 : ℝ)..t,
        reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) (γ u.toNNReal) i i ∧
      t⁻¹ * ∫ u in (0 : ℝ)..t,
        reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) (γ u.toNNReal) i i ≤ 3 := by
    intro t ht
    let f : ℝ → ℝ := fun u => reducedCoefficient (EinsteinFull.Work.W8.physicalPair i W) (γ u.toNNReal) i i
    have hf : Continuous f := by
      exact (((reduce (EinsteinFull.Work.W8.physicalPair i W)).1.continuous.comp
        (γ.continuous.comp continuous_real_toNNReal)).matrix_elem i i)
    have hlow : 0 ≤ ∫ u in (0 : ℝ)..t, f u :=
      intervalIntegral.integral_nonneg ht.le (fun u _ => (hb _).1)
    have hhigh : (∫ u in (0 : ℝ)..t, f u) ≤ t * 3 := by
      have h := intervalIntegral.integral_mono_on ht.le (hf.intervalIntegrable (μ := volume) _ _)
        (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => (3 : ℝ)) volume 0 t)
        (fun u _ => (hb _).2)
      simpa using h
    constructor
    · exact mul_nonneg (inv_nonneg.mpr ht.le) hlow
    · have h := mul_le_mul_of_nonneg_left hhigh (inv_nonneg.mpr ht.le)
      rw [← mul_assoc, inv_mul_cancel₀ ht.ne', one_mul] at h
      exact h
  have havg0 : 0 ≤ avg := ge_of_tendsto hγ (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht; exact (htbound t ht).1)
  have havg3 : avg ≤ 3 := le_of_tendsto hγ (by filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht; exact (htbound t ht).2)
  have habs : |avg| ≤ 3 := by rw [abs_of_nonneg havg0]; exact havg3
  refine ⟨η, avg, hrate, heq, habs, ?_⟩
  have ha : |avg - 1| ≤ 4 := by rw [abs_le]; constructor <;> linarith
  have hc := (EinsteinFull.Work.W8.clockParameter_pos i).le
  rw [heq]
  have hid : 1 - EinsteinFull.Work.W8.clockParameter i * lam * (avg - 1) - 1 =
      -(EinsteinFull.Work.W8.clockParameter i * lam * (avg - 1)) := by ring
  rw [hid, abs_neg, abs_mul, abs_mul, abs_of_nonneg hc]
  nlinarith [abs_nonneg lam, mul_nonneg hc (abs_nonneg lam)]


/-- Small signed forces give uniform bounds for the actual clock rate. -/
theorem sharp_actual_clock_rate_bounds_for_small_force_from_graph
    (h0 : node_app_u3A_sharp_u2D_harmonicStmt)
    (h1 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h2 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω)))
    (hsmall : |lam| ≤ (8 * EinsteinFull.Work.W8.clockParameter
      (⟨0, by omega⟩ : Fin d))⁻¹) :
    ∃ η avg : ℝ, HasReducedClockRate Q Y η ∧
      η = 1 - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * lam * (avg-1) ∧
      |avg| ≤ 3 ∧ (1/2 : ℝ) ≤ η ∧ η ≤ (3/2 : ℝ) := by
  obtain ⟨η, avg, hrate, heq, havg, hbound⟩ :=
    sharp_actual_clock_rate_linear_force_bound_from_graph h0 h1 h2 d hd P hP D Q hQ lam hlam Y hY
  have hpos : 0 < 8 * EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) :=
    mul_pos (by norm_num) (EinsteinFull.Work.W8.clockParameter_pos _)
  have hprod := mul_le_mul_of_nonneg_left hsmall hpos.le
  rw [mul_inv_cancel₀ hpos.ne'] at hprod
  have hhalf : |η - 1| ≤ (1/2 : ℝ) := by nlinarith [hbound]
  refine ⟨η, avg, hrate, heq, havg, ?_, ?_⟩
  · linarith [neg_le_of_abs_le hhalf]
  · linarith [le_of_abs_le hhalf]


/-- The inverse actual clock rate is stable under small signed forces. -/
theorem sharp_actual_inverse_clock_rate_linear_force_bound_from_graph
    (h0 : node_app_u3A_sharp_u2D_harmonicStmt)
    (h1 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h2 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω)))
    (hsmall : |lam| ≤ (8 * EinsteinFull.Work.W8.clockParameter
      (⟨0, by omega⟩ : Fin d))⁻¹) :
    ∃ η avg : ℝ, HasReducedClockRate Q Y η ∧
      η = 1 - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * lam * (avg-1) ∧
      |avg| ≤ 3 ∧ 0 < η ∧ |η⁻¹-1| ≤
        8 * EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * |lam| := by
  obtain ⟨η, avg, hrate, heq, havg, hbound⟩ :=
    sharp_actual_clock_rate_linear_force_bound_from_graph h0 h1 h2 d hd P hP D Q hQ lam hlam Y hY
  have hpos : 0 < 8 * EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) :=
    mul_pos (by norm_num) (EinsteinFull.Work.W8.clockParameter_pos _)
  have hprod := mul_le_mul_of_nonneg_left hsmall hpos.le
  rw [mul_inv_cancel₀ hpos.ne'] at hprod
  have hhalf : |η - 1| ≤ (1/2 : ℝ) := by nlinarith [hbound]
  have heta : (1/2 : ℝ) ≤ η := by linarith [neg_le_of_abs_le hhalf]
  have heta_pos : 0 < η := by linarith
  refine ⟨η, avg, hrate, heq, havg, heta_pos, ?_⟩
  have hinv : η⁻¹ ≤ 2 := by
    have h : (1 : ℝ) * η⁻¹ ≤ 2 := (mul_inv_le_iff₀ heta_pos).2 (by linarith)
    simpa using h
  have hid : η⁻¹ - 1 = -(η - 1) * η⁻¹ := by
    field_simp [ne_of_gt heta_pos]
    <;> ring
  rw [hid, abs_mul, abs_neg, abs_of_pos (inv_pos.mpr heta_pos)]
  have hrhs : 0 ≤ 4 * EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * |lam| :=
    mul_nonneg (mul_nonneg (by norm_num) (EinsteinFull.Work.W8.clockParameter_pos _).le) (abs_nonneg _)
  have hm := mul_le_mul hbound hinv (inv_nonneg.mpr heta_pos.le) hrhs
  nlinarith [hm, abs_nonneg lam, (EinsteinFull.Work.W8.clockParameter_pos (⟨0, by omega⟩ : Fin d)).le]

/-- The actual clock ratio has a quadratic error for small signed forces. -/
theorem sharp_actual_clock_ratio_quadratic_force_error_from_graph
    (h0 : node_app_u3A_sharp_u2D_harmonicStmt)
    (h1 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h2 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω)))
    (hsmall : |lam| ≤ (8 * EinsteinFull.Work.W8.clockParameter
      (⟨0, by omega⟩ : Fin d))⁻¹) :
    ∃ η avg : ℝ, HasReducedClockRate Q Y η ∧
      η = 1 - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * lam * (avg-1) ∧
      |avg| ≤ 3 ∧ 0 < η ∧ |lam / η - lam| ≤
        8 * EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * |lam| ^ 2 := by
  obtain ⟨η, avg, hrate, heq, havg, heta, hbound⟩ :=
    sharp_actual_inverse_clock_rate_linear_force_bound_from_graph
      h0 h1 h2 d hd P hP D Q hQ lam hlam Y hY hsmall
  refine ⟨η, avg, hrate, heq, havg, heta, ?_⟩
  have hid : lam / η - lam = lam * (η⁻¹ - 1) := by rw [div_eq_mul_inv]; ring
  rw [hid, abs_mul]
  calc
    |lam| * |η⁻¹ - 1| ≤ |lam| *
        (8 * EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * |lam|) :=
      mul_le_mul_of_nonneg_left hbound (abs_nonneg lam)
    _ = 8 * EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * |lam| ^ 2 := by ring

/-- The actual clock ratio has a cubic remainder after its quadratic term. -/
theorem sharp_actual_clock_ratio_cubic_remainder_from_graph
    (h0 : node_app_u3A_sharp_u2D_harmonicStmt)
    (h1 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h2 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω)))
    (hsmall : |lam| ≤ (8 * EinsteinFull.Work.W8.clockParameter
      (⟨0, by omega⟩ : Fin d))⁻¹) :
    ∃ η avg : ℝ, HasReducedClockRate Q Y η ∧
      η = 1 - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * lam * (avg-1) ∧
      |avg| ≤ 3 ∧ 0 < η ∧ |lam / η - lam| ≤
        8 * EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * |lam| ^ 2 ∧
      |lam / η - lam - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * (avg-1) * lam^2| ≤
        32 * (EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d))^2 * |lam|^3 := by
  obtain ⟨η, avg, hrate, heq, havg, heta, hquad⟩ :=
    sharp_actual_clock_ratio_quadratic_force_error_from_graph
      h0 h1 h2 d hd P hP D Q hQ lam hlam Y hY hsmall
  refine ⟨η, avg, hrate, heq, havg, heta, hquad, ?_⟩
  have havg' : |avg - 1| ≤ 4 := by
    have h := abs_sub avg 1
    simp only [abs_one] at h
    linarith
  have hc : 0 ≤ EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) :=
    (EinsteinFull.Work.W8.clockParameter_pos _).le
  have hid : lam / η - lam - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * (avg - 1) * lam^2 =
      (lam / η - lam) * (EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * lam * (avg - 1)) := by
    field_simp [ne_of_gt heta]
    rw [heq]
    <;> ring
  rw [hid, abs_mul, abs_mul, abs_mul, abs_of_nonneg hc]
  have hm := mul_le_mul_of_nonneg_left havg' (mul_nonneg hc (abs_nonneg lam))
  have hm' := mul_le_mul hquad hm
    (mul_nonneg (mul_nonneg hc (abs_nonneg lam)) (abs_nonneg (avg - 1)))
    (mul_nonneg (mul_nonneg (by norm_num) hc) (sq_nonneg |lam|))
  nlinarith [hm', abs_nonneg lam, sq_nonneg |lam|, sq_nonneg (EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d))]


/-- The normalized clock-ratio error is controlled at first order in the force. -/
theorem sharp_actual_clock_ratio_normalized_second_order_bound_from_graph
    (h0 : node_app_u3A_sharp_u2D_harmonicStmt)
    (h1 : node_app_u3A_sharp_u2D_fieldsStmt)
    (h2 : node_eq_u2E_time_u2D_change_u2D_identitiesStmtV2)
    (d : ℕ) (hd : 2 ≤ d) (P : Measure (NoiseSample d))
    (hP : External.IsWhiteNoiseLaw P) (D : StructuralData d)
    (Q : EnvironmentLaw d D.ellipticity D.dependenceRange)
    (hQ : Q.measure = P.map (EinsteinFull.Work.W8.physicalPair (⟨0, by omega⟩ : Fin d)))
    (lam : ℝ) (hlam : lam ≠ 0) (Y : QuenchedPathLaws d)
    (hY : ∀ᵐ ω ∂Q.measure, SolvesMartingaleProblem
      (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam) 0 (Y (0, ω)))
    (hsmall : |lam| ≤ (8 * EinsteinFull.Work.W8.clockParameter
      (⟨0, by omega⟩ : Fin d))⁻¹) :
    ∃ η avg : ℝ, HasReducedClockRate Q Y η ∧
      η = 1 - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * lam * (avg-1) ∧
      |avg| ≤ 3 ∧ 0 < η ∧ |lam / η - lam| ≤
        8 * EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * |lam| ^ 2 ∧
      |((lam/η - lam)/lam^2) - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d)*(avg-1)| ≤
        32*(EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d))^2*|lam| := by
  obtain ⟨η, avg, hrate, heq, havg, heta, hquad, hcubic⟩ :=
    sharp_actual_clock_ratio_cubic_remainder_from_graph
      h0 h1 h2 d hd P hP D Q hQ lam hlam Y hY hsmall
  refine ⟨η, avg, hrate, heq, havg, heta, hquad, ?_⟩
  have hp : 0 < lam ^ 2 := sq_pos_of_ne_zero hlam
  have hid : (lam / η - lam) / lam ^ 2 -
      EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) * (avg - 1) =
      (lam / η - lam - EinsteinFull.Work.W8.clockParameter (⟨0, by omega⟩ : Fin d) *
        (avg - 1) * lam ^ 2) / lam ^ 2 := by
    field_simp [ne_of_gt hp]
    <;> ring
  rw [hid, abs_div, abs_of_pos hp]
  apply (div_le_iff₀ hp).2
  have habs : |lam| ^ 2 = lam ^ 2 := sq_abs lam
  rw [← habs]
  rw [← habs] at hcubic
  nlinarith [hcubic]

end EinsteinFull.Blueprint
