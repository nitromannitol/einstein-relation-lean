import EinsteinRelation.Diffusion.JointClockPathMapSupport
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# The inverse-clock path map is injective, with a measurable left inverse

For a regular physical environment `ω` and a continuous path `γ`, the path
`inverseClockPath ω γ = γ ∘ A⁻¹` (with `A(t) = ∫₀ᵗ exp(-2 ω.2 (γ u)) du`) is mapped back
to `γ` by the same construction for the sign-flipped potential: the clock of
`X = γ ∘ A⁻¹` for the density `exp(2 ω.2 ·)` is `A⁻¹` itself (change of variables
`u = A r`). Consequently two laws with the same inverse-clock image coincide.
-/

open MeasureTheory Filter Set
open scoped NNReal Topology

noncomputable section
namespace EinsteinFull
open EinsteinRelation EinsteinRelation.Clock EinsteinRelation.Clock.InverseMeaningV3

/-- The environment with the sign of the scalar potential reversed. -/
def flipPotential {d : ℕ} (ω : FieldPair d) : FieldPair d := (ω.1, -ω.2)

theorem flipPotential_apply {d : ℕ} (ω : FieldPair d) (x : Vec d) :
    (flipPotential ω).2 x = -ω.2 x := rfl

theorem isRegular_flipPotential {d : ℕ} {L : ℝ} {ω : FieldPair d} (hω : IsRegular L ω) :
    IsRegular L (flipPotential ω) := by
  obtain ⟨h1, h2, h3, h4⟩ := hω
  refine ⟨h1, fun x => ?_, h3, fun x y => ?_⟩
  · rw [flipPotential_apply, abs_neg]
    exact h2 x
  · have e : (flipPotential ω).2 x - (flipPotential ω).2 y = ω.2 y - ω.2 x := by
      rw [flipPotential_apply, flipPotential_apply]
      ring
    rw [e, abs_sub_comm]
    exact h4 x y

theorem coe_physicalPathClock_flip {d : ℕ} (ω : FieldPair d) (γ : Path d) (s : ℝ≥0) :
    (physicalPathClock (flipPotential ω) γ s : ℝ) =
      ∫ u in (0 : ℝ)..(s : ℝ), Real.exp (2 * ω.2 (γ u.toNNReal)) := by
  rw [coe_physicalPathClock_explicit]
  refine intervalIntegral.integral_congr (fun u _ => ?_)
  show Real.exp (-2 * (flipPotential ω).2 (γ u.toNNReal)) =
    Real.exp (2 * ω.2 (γ u.toNNReal))
  rw [flipPotential_apply]
  congr 1
  ring

/-- The sign-flipped clock of the inverse-clock path is the inverse clock. -/
theorem physicalPathClock_flip_inverseClockPath {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) (s : ℝ≥0) :
    physicalPathClock (flipPotential ω) (inverseClockPath ω γ L hω) s =
      inversePhysicalPathClock ω γ L hω s := by
  apply NNReal.eq
  rw [coe_physicalPathClock_flip]
  set τ : ℝ := (inversePhysicalPathClock ω γ L hω s : ℝ) with hτ
  let f : ℝ → ℝ := fun u => Real.exp (-2 * ω.2 (γ u.toNNReal))
  have hfc : Continuous f :=
    Real.continuous_exp.comp (continuous_const.mul
      (ω.2.continuous.comp (γ.continuous.comp continuous_real_toNNReal)))
  let a : ℝ → ℝ := fun r => ∫ u in (0 : ℝ)..r, f u
  have ha : ∀ r : ℝ, HasDerivAt a (f r) r :=
    fun r => (hfc.integral_hasStrictDerivAt 0 r).hasDerivAt
  have ha_eq : ∀ r : ℝ, 0 ≤ r → a r = (physicalPathClock ω γ r.toNNReal : ℝ) := by
    intro r hr
    have h := coe_physicalPathClock_explicit ω γ r.toNNReal
    rw [Real.coe_toNNReal r hr] at h
    exact h.symm
  have hτ0 : 0 ≤ τ := NNReal.coe_nonneg _
  have haτ : a τ = (s : ℝ) := by
    rw [ha_eq τ hτ0]
    have h : τ.toNNReal = inversePhysicalPathClock ω γ L hω s := Real.toNNReal_coe
    rw [h, physicalPathClock_inversePhysicalPathClock]
  have ha0 : a 0 = 0 := intervalIntegral.integral_same
  let g : ℝ → ℝ := fun u =>
    Real.exp (2 * ω.2 ((inverseClockPath ω γ L hω) u.toNNReal))
  have hgc : Continuous g :=
    Real.continuous_exp.comp (continuous_const.mul
      (ω.2.continuous.comp ((inverseClockPath ω γ L hω).continuous.comp
        continuous_real_toNNReal)))
  have hsub := intervalIntegral.integral_comp_mul_deriv (a := 0) (b := τ) (f := a) (f' := f)
    (g := g) (fun x _ => ha x) hfc.continuousOn hgc
  rw [ha0, haτ] at hsub
  have hone : ∀ x ∈ uIcc (0 : ℝ) τ, (g ∘ a) x * f x = 1 := by
    intro x hx
    rw [uIcc_of_le hτ0] at hx
    have hx0 : 0 ≤ x := hx.1
    simp only [Function.comp_apply, g, f]
    rw [ha_eq x hx0, Real.toNNReal_coe, inverseClockPath_atPhysicalClock, ← Real.exp_add,
      show 2 * ω.2 (γ x.toNNReal) + -2 * ω.2 (γ x.toNNReal) = 0 by ring, Real.exp_zero]
  have hint : (∫ x in (0 : ℝ)..τ, (g ∘ a) x * f x) = τ := by
    rw [intervalIntegral.integral_congr (g := fun _ => (1 : ℝ)) hone]
    simp
  rw [hint] at hsub
  exact hsub.symm

/-- Applying the sign-flipped inverse-clock construction undoes the inverse-clock path. -/
theorem inverseClockPath_flip_inverseClockPath {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) :
    inverseClockPath (flipPotential ω) (inverseClockPath ω γ L hω) L
      (isRegular_flipPotential hω) = γ := by
  apply ContinuousMap.ext
  intro t
  have hs := physicalPathClock_flip_inverseClockPath ω γ L hω (physicalPathClock ω γ t)
  rw [inversePhysicalPathClock_physicalPathClock] at hs
  change (inverseClockPath ω γ L hω)
    (inversePhysicalPathClock (flipPotential ω) (inverseClockPath ω γ L hω) L
      (isRegular_flipPotential hω) t) = γ t
  rw [inversePhysicalPathClock_unique (flipPotential ω) (inverseClockPath ω γ L hω) L
    (isRegular_flipPotential hω) t (physicalPathClock ω γ t) hs]
  exact inverseClockPath_atPhysicalClock ω γ L hω t

/-- The inverse-clock path map at a fixed regular environment is measurable. -/
theorem measurable_inverseClockPath_fixed {d : ℕ} (ω : FieldPair d) (L : ℝ)
    (hω : IsRegular L ω) :
    Measurable (fun γ : Path d => inverseClockPath ω γ L hω) := by
  have h := (Clock.PathMapV4.measurable_inverseClockPathMap (d := d) (L := L)).comp
    (measurable_const.prodMk measurable_id :
      Measurable (fun γ : Path d => ((⟨ω, hω⟩ : ReductionImageV3.PhysicalField d L), γ)))
  exact h

/-- Two path laws with the same inverse-clock image at a regular environment coincide. -/
theorem pathLaw_eq_of_inverseClock_map_eq {d : ℕ} (ω : FieldPair d) (L : ℝ)
    (hω : IsRegular L ω) (P P' : Measure (Path d))
    (h : Measure.map (fun γ : Path d => inverseClockPath ω γ L hω) P =
      Measure.map (fun γ : Path d => inverseClockPath ω γ L hω) P') : P = P' := by
  have hω' := isRegular_flipPotential hω
  have hinv := measurable_inverseClockPath_fixed ω L hω
  have hflip := measurable_inverseClockPath_fixed (flipPotential ω) L hω'
  have hid : (fun X : Path d => inverseClockPath (flipPotential ω) X L hω') ∘
      (fun γ : Path d => inverseClockPath ω γ L hω) = id := by
    funext γ
    exact inverseClockPath_flip_inverseClockPath ω γ L hω
  have key : ∀ R : Measure (Path d), Measure.map
      (fun X : Path d => inverseClockPath (flipPotential ω) X L hω')
      (Measure.map (fun γ : Path d => inverseClockPath ω γ L hω) R) = R := by
    intro R
    rw [Measure.map_map hflip hinv, hid, Measure.map_id]
  rw [← key P, ← key P', h]

end EinsteinFull
