import EinsteinRelation.Diffusion.Basic
import EinsteinRelation.Diffusion.ClockInverseSupport
import EinsteinRelation.Diffusion.JointClockPathMapSupport
import Mathlib.Tactic.LinearCombination

/-! # The velocity time-change identity

`paper/main.tex` 215-233. The reduced path `Y` and the physical path `X` are related
pathwise by `X(A(t)) = Y(t)`, where `A` is the physical clock. The clock rate
`η = lim A(t)/t` is the ratio of the first coordinates of the two velocities, and the
reduced velocity is `η` times the physical velocity, `ℓ_X = η⁻¹ ℓ` (main.tex 230).

The pathwise statement is generic in the time change `A`. The quenched statement
transfers the physical velocity through the image of the reduced law under the inverse
clock, and applies the pathwise statement to the physical clock of each reduced path.
-/

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinRelation

/-- The Euclidean pairing with a coordinate unit vector reads off that coordinate. -/
private theorem dot_unitVector_eq_apply {d : ℕ} (i : Fin d) (w : Vec d) :
    dot (unitVector i) w = w i := by
  simp [dot, unitVector, Pi.single_apply]

/-- Pathwise time change. If `X(A t) = Y t` with `A → ∞`, and both paths have velocities
with the `i`-th coordinate of `vX` positive, then `A t / t` converges to the ratio of the
`i`-th coordinates of the velocities, and the velocity of `Y` is that ratio times `vX`. -/
theorem hasPathVelocity_timeChange {d : ℕ} {X Y : Path d} {A : ℝ≥0 → ℝ≥0}
    (hXA : ∀ t, X (A t) = Y t)
    (hA : Tendsto (fun t => (A t : ℝ)) atTop atTop) {vX vY : Vec d} {i : Fin d}
    (hX : HasPathVelocity X vX) (hY : HasPathVelocity Y vY)
    (hpos : 0 < dot (unitVector i) vX) (hA0 : ∀ᶠ t in atTop, 0 < (A t : ℝ)) :
    Tendsto (fun t : ℝ≥0 => (A t : ℝ) / t) atTop
      (𝓝 (dot (unitVector i) vY / dot (unitVector i) vX)) ∧
    vY = (dot (unitVector i) vY / dot (unitVector i) vX) • vX := by
  simp only [dot_unitVector_eq_apply] at hpos ⊢
  have hAtop : Tendsto A atTop atTop := NNReal.tendsto_coe_atTop.mp hA
  have hX' : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • X t) atTop (𝓝 vX) := hX
  have hY' : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • Y t) atTop (𝓝 vY) := hY
  -- the physical velocity sampled at the clock time `A t`
  have hXc : Tendsto (fun t : ℝ≥0 => (A t : ℝ)⁻¹ • X (A t)) atTop (𝓝 vX) :=
    hX'.comp hAtop
  have hXi : Tendsto (fun t : ℝ≥0 => ((A t : ℝ)⁻¹ • X (A t)) i) atTop (𝓝 (vX i)) :=
    tendsto_pi_nhds.1 hXc i
  have hYi : Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ • Y t) i) atTop (𝓝 (vY i)) :=
    tendsto_pi_nhds.1 hY' i
  have hXi_pos : ∀ᶠ t in atTop, 0 < ((A t : ℝ)⁻¹ • X (A t)) i :=
    (tendsto_order.1 hXi).1 0 hpos
  have hratio : Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ • Y t) i / ((A t : ℝ)⁻¹ • X (A t)) i)
      atTop (𝓝 (vY i / vX i)) :=
    hYi.div hXi hpos.ne'
  -- the `i`-th coordinate of `Y t / t` is `A t / t` times that of `X (A t) / A t`
  have hcoord : ∀ᶠ t in atTop,
      (A t : ℝ) / t * ((A t : ℝ)⁻¹ • X (A t)) i = ((t : ℝ)⁻¹ • Y t) i := by
    filter_upwards [hA0] with t ht
    show (A t : ℝ) / t * ((A t : ℝ)⁻¹ • X (A t)) i = ((t : ℝ)⁻¹ • Y t) i
    have hA' : (A t : ℝ) * (A t : ℝ)⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    rw [← hXA t]
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination ((t : ℝ)⁻¹ * X (A t) i) * hA'
  have hfirst : Tendsto (fun t : ℝ≥0 => (A t : ℝ) / t) atTop (𝓝 (vY i / vX i)) := by
    refine Tendsto.congr' ?_ hratio
    filter_upwards [hcoord, hXi_pos] with t h1 h2
    exact (div_eq_iff h2.ne').mpr h1.symm
  -- the vector identity `Y t / t = (A t / t) • (X (A t) / A t)` for large `t`
  have hvec : (fun t : ℝ≥0 => (t : ℝ)⁻¹ • Y t) =ᶠ[atTop]
      (fun t : ℝ≥0 => ((A t : ℝ) / t) • ((A t : ℝ)⁻¹ • X (A t))) := by
    filter_upwards [hA0] with t ht
    show (t : ℝ)⁻¹ • Y t = ((A t : ℝ) / t) • ((A t : ℝ)⁻¹ • X (A t))
    have hA' : (A t : ℝ) * (A t : ℝ)⁻¹ = 1 := mul_inv_cancel₀ ht.ne'
    have hc : (A t : ℝ) / t * (A t : ℝ)⁻¹ = (t : ℝ)⁻¹ := by
      linear_combination (t : ℝ)⁻¹ * hA'
    rw [hXA t, smul_smul, hc]
  refine ⟨hfirst, ?_⟩
  exact tendsto_nhds_unique (Tendsto.congr' hvec hY') (hfirst.smul hXc)

/-- The time-change identity for one environment and one reduced path, with the physical
clock as the time change. The regularity witness supplies the bounds that make the clock
diverge, so `A t / t` is positive and tends to infinity. -/
private theorem physicalClock_velocity {d : ℕ} (ω : FieldPair d) (γ : Path d) (L : ℝ)
    (hω : IsRegular L ω) {vX vY : Vec d} {i : Fin d}
    (hX : HasPathVelocity (Clock.InverseMeaningV3.inverseClockPath ω γ L hω) vX)
    (hY : HasPathVelocity γ vY) (hpos : 0 < dot (unitVector i) vX) :
    Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop
      (𝓝 (dot (unitVector i) vY / dot (unitVector i) vX)) ∧
    vY = (dot (unitVector i) vY / dot (unitVector i) vX) • vX := by
  have hA : Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr (Clock.physicalPathClock_tendsto_atTop ω γ L hω.2.1)
  exact hasPathVelocity_timeChange (X := Clock.InverseMeaningV3.inverseClockPath ω γ L hω)
    (Y := γ) (A := Clock.physicalPathClock ω γ)
    (Clock.InverseMeaningV3.inverseClockPath_atPhysicalClock ω γ L hω) hA hX hY hpos
    (hA.eventually_gt_atTop 0)

/-- Quenched time-change identity. The physical quenched velocity `vX` transfers to the
inverse-clock images of the reduced law, so the pathwise identity applies to almost every
environment and almost every reduced path. With `η` the ratio of the `i`-th coordinates of
`vY` and `vX`, the physical clock of a reduced path has rate `η` and the reduced velocity
is `vY = η • vX`, that is `ℓ_X = η⁻¹ ℓ` (main.tex 230). -/
theorem quenchedVelocity_timeChange {d : ℕ} (Q : Measure (FieldPair d)) [IsProbabilityMeasure Q]
    (L : ℝ) (P P' : ProbabilityTheory.Kernel (FieldPair d) (Path d))
    (hreg : ∀ᵐ ω ∂Q, IsRegular L ω)
    (hP : ∀ᵐ ω ∂Q, IsProbabilityMeasure (P ω)) (hP' : ∀ᵐ ω ∂Q, IsProbabilityMeasure (P' ω))
    (hTC : ∀ᵐ ω ∂Q, ∀ hω : IsRegular L ω,
      P ω = Measure.map (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ L hω) (P' ω))
    {vX vY : Vec d} {i : Fin d} (hX : HasQuenchedVelocity Q P vX)
    (hY : HasQuenchedVelocity Q P' vY) (hpos : 0 < dot (unitVector i) vX) :
    vY = (dot (unitVector i) vY / dot (unitVector i) vX) • vX ∧
      ∀ᵐ ω ∂Q, ∀ᵐ γ ∂P' ω,
        Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ) / t) atTop
          (𝓝 (dot (unitVector i) vY / dot (unitVector i) vX)) := by
  have hX' : ∀ᵐ ω ∂Q, ∀ᵐ γ ∂P ω, HasPathVelocity γ vX := hX
  have hY' : ∀ᵐ ω ∂Q, ∀ᵐ γ ∂P' ω, HasPathVelocity γ vY := hY
  -- the image of the reduced law under the inverse clock is the physical law, so almost
  -- every reduced path is sent to a path with physical velocity `vX`
  have hmap : ∀ᵐ ω ∂Q, ∀ hω : IsRegular L ω,
      ∀ᵐ γ ∂P' ω, HasPathVelocity (Clock.InverseMeaningV3.inverseClockPath ω γ L hω) vX := by
    filter_upwards [hP, hTC, hX'] with ω hωP hωTC hωX
    intro hω
    haveI : IsProbabilityMeasure (P ω) := hωP
    -- the inverse clock path is measurable in the reduced path, jointly with the regular input
    have hmeas : AEMeasurable (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ L hω)
        (P' ω) :=
      ((Clock.PathMapV4.measurable_inverseClockPathMap (d := d) (L := L)).comp
        (measurable_const (a := (⟨ω, hω⟩ : Clock.PathMapV4.PhysicalInput d L)).prodMk
          measurable_id)).aemeasurable
    have hωX' : ∀ᵐ γ ∂(Measure.map (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ L hω)
        (P' ω)), HasPathVelocity γ vX := by
      rw [← hωTC hω]
      exact hωX
    exact ae_of_ae_map hmeas hωX'
  refine ⟨?_, ?_⟩
  · obtain ⟨ω, hωreg, hωP', hωmap, hωY⟩ := (hreg.and (hP'.and (hmap.and hY'))).exists
    haveI : IsProbabilityMeasure (P' ω) := hωP'
    obtain ⟨γ, hγX, hγY⟩ := ((hωmap hωreg).and hωY).exists
    exact (physicalClock_velocity ω γ L hωreg hγX hγY hpos).2
  · filter_upwards [hreg, hmap, hY'] with ω hωreg hωmap hωY
    filter_upwards [hωmap hωreg, hωY] with γ hγX hγY
    exact (physicalClock_velocity ω γ L hωreg hγX hγY hpos).1

end EinsteinRelation
