import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_generator_u23_pathwise
import EinsteinFull.Frozen.ReducedClockRate
import EinsteinRelation.Diffusion.VelocityTimeChange

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation

/-- Time-change ratios only require a nonzero physical velocity coordinate. -/
private theorem hasPathVelocity_timeChange_nonzero {d : ℕ} {X Y : Path d} {A : ℝ≥0 → ℝ≥0}
    (hXA : ∀ t, X (A t) = Y t)
    (hA : Tendsto (fun t => (A t : ℝ)) atTop atTop) {vX vY : Vec d} {i : Fin d}
    (hX : HasPathVelocity X vX) (hY : HasPathVelocity Y vY)
    (hne : vX i ≠ 0) (hA0 : ∀ᶠ t in atTop, 0 < (A t : ℝ)) :
    Tendsto (fun t : ℝ≥0 => (A t : ℝ) / t) atTop
      (𝓝 (vY i / vX i)) ∧
    vY = (vY i / vX i) • vX := by
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
  have hXi_ne : ∀ᶠ t in atTop, ((A t : ℝ)⁻¹ • X (A t)) i ≠ 0 :=
    hXi.eventually_ne hne
  have hratio : Tendsto (fun t : ℝ≥0 => ((t : ℝ)⁻¹ • Y t) i / ((A t : ℝ)⁻¹ • X (A t)) i)
      atTop (𝓝 (vY i / vX i)) :=
    hYi.div hXi hne
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
    filter_upwards [hcoord, hXi_ne] with t h1 h2
    exact (div_eq_iff h2).mpr h1.symm
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

private theorem physicalClock_velocity_nonzero {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) {vX vY : Vec d} {i : Fin d}
    (hX : HasPathVelocity (Clock.InverseMeaningV3.inverseClockPath ω γ L hω) vX)
    (hY : HasPathVelocity γ vY) (hne : vX i ≠ 0) :
    Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ (vY i / vX i) ∧
      vY = (vY i / vX i) • vX := by
  have hA : Tendsto (fun t : ℝ≥0 => (Clock.physicalPathClock ω γ t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr (Clock.physicalPathClock_tendsto_atTop ω γ L hω.2.1)
  exact hasPathVelocity_timeChange_nonzero
    (Clock.InverseMeaningV3.inverseClockPath_atPhysicalClock ω γ L hω)
    hA hX hY hne (hA.eventually_gt_atTop 0)

/-- Actual-law signed velocity transport, conditional on both deterministic velocities. -/
theorem c9_signed_velocity_timechange_of_actual_laws
    (hpathwise : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (lam : ℝ) (X Y : QuenchedPathLaws d)
    (hXMP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (X (0, ω)))
    (hYMP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (vX vY : Vec d)
    (hX : HasQuenchedVelocity Q.measure (originLaw X) vX)
    (hY : HasQuenchedVelocity Q.measure (originLaw Y) vY)
    (hsigned : 0 < lam * vX ⟨0, by omega⟩) :
    ∃ η : ℝ, HasReducedClockRate Q Y η ∧
      η ∈ Set.Icc (Real.exp (-2 * Λ)) (Real.exp (2 * Λ)) ∧
      vY = η • vX ∧ 0 < lam * vY ⟨0, by omega⟩ := by
  let i : Fin d := ⟨0, by omega⟩
  let η : ℝ := vY i / vX i
  have hne : vX i ≠ 0 := by
    intro hz
    have : lam * vX i = 0 := by rw [hz, mul_zero]
    exact (ne_of_gt hsigned) this
  have hTC := (hpathwise d hd Λ r Q i lam).2 X Y hXMP hYMP
  have hmap : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ ω,
      ∀ᵐ γ ∂originLaw Y ω,
        HasPathVelocity (Clock.InverseMeaningV3.inverseClockPath ω γ Λ hω) vX := by
    filter_upwards [hTC, hX] with ω hωTC hωX
    intro hω
    have hmeas : AEMeasurable
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ hω) (originLaw Y ω) :=
      ((Clock.PathMapV4.measurable_inverseClockPathMap (d := d) (L := Λ)).comp
        (measurable_const (a := (⟨ω, hω⟩ : Clock.PathMapV4.PhysicalInput d Λ)).prodMk
          measurable_id)).aemeasurable
    have hωX' : ∀ᵐ γ ∂(Measure.map
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ hω) (originLaw Y ω)),
        HasPathVelocity γ vX := by
      rw [originLaw_apply, ← (hωTC hω).1]
      exact hωX
    exact ae_of_ae_map hmeas hωX'
  have hrate : HasReducedClockRate Q Y η := by
    filter_upwards [Q.regular, hmap, hY] with ω hωreg hωmap hωY
    filter_upwards [hωmap hωreg, hωY] with γ hγX hγY
    exact (physicalClock_velocity_nonzero ω γ Λ hωreg hγX hγY hne).1
  obtain ⟨ω, hωreg, hωMP, hωmap, hωY⟩ :=
    (Q.regular.and (hYMP.and (hmap.and hY))).exists
  have : IsProbabilityMeasure (originLaw Y ω) := hωMP.1
  obtain ⟨γ, hγX, hγY⟩ := ((hωmap hωreg).and hωY).exists
  obtain ⟨hγlim, hvY⟩ := physicalClock_velocity_nonzero ω γ Λ hωreg hγX hγY hne
  have hlo : ∀ᶠ t : ℝ≥0 in atTop,
      Real.exp (-2 * Λ) ≤ (Clock.physicalPathClock ω γ t : ℝ) / t := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    exact (le_div_iff₀ (NNReal.coe_pos.mpr ht)).2
      (Clock.InverseMeaningV3.physicalPathClock_bounds ω γ Λ hωreg.2.1 t).1
  have hhi : ∀ᶠ t : ℝ≥0 in atTop,
      (Clock.physicalPathClock ω γ t : ℝ) / t ≤ Real.exp (2 * Λ) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    exact (div_le_iff₀ (NNReal.coe_pos.mpr ht)).2
      (Clock.InverseMeaningV3.physicalPathClock_bounds ω γ Λ hωreg.2.1 t).2
  have hηlo : Real.exp (-2 * Λ) ≤ η := ge_of_tendsto hγlim hlo
  have hηhi : η ≤ Real.exp (2 * Λ) := le_of_tendsto hγlim hhi
  have hηpos : 0 < η := lt_of_lt_of_le (Real.exp_pos _) hηlo
  refine ⟨η, hrate, ⟨hηlo, hηhi⟩, hvY, ?_⟩
  change 0 < lam * vY i
  rw [hvY, Pi.smul_apply, smul_eq_mul]
  calc
    0 < η * (lam * vX i) := mul_pos hηpos hsigned
    _ = lam * (η * vX i) := by ring

private theorem hasPathVelocity_of_timeChange_clockRate {d : ℕ}
    {X Y : Path d} {A : ℝ≥0 → ℝ≥0} {vX : Vec d} {η : ℝ}
    (hXA : ∀ t, X (A t) = Y t)
    (hA : Tendsto A atTop atTop) (hX : HasPathVelocity X vX)
    (hηpos : 0 < η)
    (hη : Tendsto (fun t : ℝ≥0 => (A t : ℝ) / t) atTop (𝓝 η)) :
    HasPathVelocity Y (η • vX) := by
  have hX' : Tendsto (fun t : ℝ≥0 => (t : ℝ)⁻¹ • X t) atTop (𝓝 vX) := hX
  have hXc := hX'.comp hA
  have hA0 : ∀ᶠ t in atTop, 0 < (A t : ℝ) := by
    filter_upwards [(tendsto_order.1 hη).1 0 hηpos] with t ht
    by_contra hn
    have hz : (A t : ℝ) = 0 := le_antisymm (not_lt.mp hn) (NNReal.coe_nonneg _)
    simp only [hz, zero_div, lt_self_iff_false] at ht
  have hvec : (fun t : ℝ≥0 => ((A t : ℝ) / t) • ((A t : ℝ)⁻¹ • X (A t)))
      =ᶠ[atTop] (fun t : ℝ≥0 => (t : ℝ)⁻¹ • Y t) := by
    filter_upwards [hA0] with t ht
    have hc : (A t : ℝ) / t * (A t : ℝ)⁻¹ = (t : ℝ)⁻¹ := by
      rw [div_eq_mul_inv, mul_right_comm, mul_inv_cancel₀ ht.ne', one_mul]
    rw [smul_smul, hc, hXA t]
  exact Tendsto.congr' hvec (hη.smul hXc)

/-- A known positive reduced clock rate transports physical velocity to the same
supplied reduced law, without assuming that reduced law already has a velocity. -/
theorem c9_reduced_velocity_of_physical_velocity_and_clock_rate
    (h0 : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmt)
    (d : ℕ) (hd : 2 ≤ d) (Λ r : ℝ) (Q : EnvironmentLaw d Λ r)
    (lam : ℝ) (X Y : QuenchedPathLaws d)
    (hXMP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (physicalGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (X (0, ω)))
    (hYMP : ∀ᵐ ω ∂Q.measure,
      SolvesMartingaleProblem (reducedGenerator (⟨0, by omega⟩ : Fin d) ω lam)
        0 (Y (0, ω)))
    (vX : Vec d) (hvX : HasQuenchedVelocity Q.measure (originLaw X) vX)
    (η : ℝ) (hηpos : 0 < η) (hη : HasReducedClockRate Q Y η) :
    HasQuenchedVelocity Q.measure (originLaw Y) (η • vX) := by
  have hTC := (h0 d hd Λ r Q (⟨0, by omega⟩ : Fin d) lam).2 X Y hXMP hYMP
  filter_upwards [Q.regular, hTC, hvX, hη] with ω hω hωTC hωX hωη
  have hmeas : AEMeasurable
      (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ hω) (originLaw Y ω) :=
    ((Clock.PathMapV4.measurable_inverseClockPathMap (d := d) (L := Λ)).comp
      (measurable_const (a := (⟨ω, hω⟩ : Clock.PathMapV4.PhysicalInput d Λ)).prodMk
        measurable_id)).aemeasurable
  have hωX' : ∀ᵐ γ ∂(Measure.map
      (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ hω) (originLaw Y ω)),
      HasPathVelocity γ vX := by
    rw [originLaw_apply, ← (hωTC hω).1]
    exact hωX
  have hmap := ae_of_ae_map hmeas hωX'
  filter_upwards [hmap, hωη] with γ hγX hγη
  exact hasPathVelocity_of_timeChange_clockRate
    (Clock.InverseMeaningV3.inverseClockPath_atPhysicalClock ω γ Λ hω)
    (Clock.physicalPathClock_tendsto_atTop ω γ Λ hω.2.1) hγX hηpos hγη

end EinsteinFull.Blueprint
