import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeForcedClock
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopeForcedLLN
import EinsteinFull.Blueprint.Foundation.Draft.S2SmoothScopePathwise
import EinsteinFull.Blueprint.Foundation.node_eq_u2E_reduced_u2D_bounds
import EinsteinFull.Frozen.SmoothEnvironment
import EinsteinRelation.Diffusion.JointClockPathMapSupport
import Mathlib.Tactic.LinearCombination

open MeasureTheory Filter
open scoped NNReal Topology

namespace EinsteinFull.Blueprint
open EinsteinRelation

-- Verbatim copy of the private lemma of `W4Reduction1.lean`.
private theorem path_clock_ratio {d : ℕ} (ω : FieldPair d) (γ : Path d)
    (L : ℝ) (hω : IsRegular L ω) {vX vY : Vec d} (i : Fin d)
    (hX : HasPathVelocity (Clock.InverseMeaningV3.inverseClockPath ω γ L hω) vX)
    (hY : HasPathVelocity γ vY) (hne : vX i ≠ 0) :
    Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ (vY i / vX i) ∧
      vY = (vY i / vX i) • vX := by
  let A := Clock.physicalPathClock ω γ
  let X := Clock.InverseMeaningV3.inverseClockPath ω γ L hω
  have hXA : ∀ t, X (A t) = γ t :=
    Clock.InverseMeaningV3.inverseClockPath_atPhysicalClock ω γ L hω
  have hAtop : Tendsto A atTop atTop :=
    Clock.physicalPathClock_tendsto_atTop ω γ L hω.2.1
  have hA : Tendsto (fun t => (A t : ℝ)) atTop atTop :=
    NNReal.tendsto_coe_atTop.mpr hAtop
  have hXc : Tendsto (fun t => (A t : ℝ)⁻¹ • X (A t)) atTop (𝓝 vX) :=
    hX.comp hAtop
  have hXi := tendsto_pi_nhds.1 hXc i
  have hYi := tendsto_pi_nhds.1 hY i
  have hratio := hYi.div hXi hne
  have hcoord : ∀ᶠ t : ℝ≥0 in atTop,
      (A t : ℝ) / t * ((A t : ℝ)⁻¹ • X (A t)) i = ((t : ℝ)⁻¹ • γ t) i := by
    filter_upwards [hA.eventually_gt_atTop 0] with t ht
    have hcancel := mul_inv_cancel₀ ht.ne'
    rw [← hXA t]
    simp only [Pi.smul_apply, smul_eq_mul]
    linear_combination ((t : ℝ)⁻¹ * X (A t) i) * hcancel
  have hfirst : Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ (vY i / vX i) := by
    refine Tendsto.congr' ?_ hratio
    filter_upwards [hcoord, hXi.eventually_ne hne] with t ht htn
    exact (div_eq_iff htn).mpr ht.symm
  have hvec : (fun t : ℝ≥0 => (t : ℝ)⁻¹ • γ t) =ᶠ[atTop]
      (fun t => ((A t : ℝ) / t) • ((A t : ℝ)⁻¹ • X (A t))) := by
    filter_upwards [hA.eventually_gt_atTop 0] with t ht
    have hc : (A t : ℝ) / t * (A t : ℝ)⁻¹ = (t : ℝ)⁻¹ := by
      linear_combination (t : ℝ)⁻¹ * mul_inv_cancel₀ ht.ne'
    rw [hXA t, smul_smul, hc]
  exact ⟨hfirst, tendsto_nhds_unique (Tendsto.congr' hvec hY) (hfirst.smul hXc)⟩

/-- Smooth-scope forced-clock identity, `Λ₀`-first: `W4Reduction1`'s proof with `hLLN := forced-lln V2`
and `hPathwise := pathwise V2`; the structural data `D` is rebuilt from `(Λ₀, r₀, b)`. -/
theorem node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clock_of_deps
    (hLLN : node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_llnStmtV2)
    (hPathwise : node_eq_u2E_reduced_u2D_generator_u23_pathwiseStmtV2)
    (hBounds : node_eq_u2E_reduced_u2D_boundsStmt) :
    node_eq_u2E_time_u2D_change_u2D_identities_u23_forced_u2D_clockStmtV2 := by
  intro Λ₀ hΛ₀
  obtain ⟨Λ, A, B, hΛ, _, _, _, hBound⟩ := hBounds Λ₀ hΛ₀
  refine ⟨Λ, hΛ, ?_⟩
  intro d hd r₀ b Q hr₀ hb hsm lam hlam X Y hX hY _hCoupling
  let i : Fin d := ⟨0, by omega⟩
  obtain ⟨vX, vY, hvX, hvY, hposX, hposY⟩ :=
    hLLN d hd Λ₀ r₀ b Q hΛ₀ hr₀ hb hsm lam hlam X Y hX hY
  have hne : vX i ≠ 0 := by
    intro hz
    have : 0 < lam * vX i := hposX
    rw [hz, mul_zero] at this
    exact lt_irrefl _ this
  let η := vY i / vX i
  have hTC : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
      X (0, ω) = (Y (0, ω)).map
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω) := by
    have h := (hPathwise d hd ⟨Λ₀, r₀, b, hΛ₀, hr₀, hb⟩ Q hsm i lam).2 X Y hX hY
    filter_upwards [h] with ω hω hreg
    exact (hω hreg).1
  have hmap : ∀ᵐ ω ∂Q.measure, ∀ hω : IsRegular Λ₀ ω,
      ∀ᵐ γ ∂Y (0, ω),
        HasPathVelocity (Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω) vX := by
    filter_upwards [hX, hTC, hvX] with ω hωX hωTC hωv
    intro hω
    haveI := hωX.1
    have heq := hωTC hω
    have hm : AEMeasurable
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω) (Y (0, ω)) := by
      exact ((Clock.PathMapV4.measurable_inverseClockPathMap (d := d) (L := Λ₀)).comp
        ((measurable_const (a := (⟨ω, hω⟩ : Clock.PathMapV4.PhysicalInput d Λ₀))).prodMk
          measurable_id)).aemeasurable
    have hv : ∀ᵐ γ ∂Measure.map
        (fun γ => Clock.InverseMeaningV3.inverseClockPath ω γ Λ₀ hω) (Y (0, ω)),
        HasPathVelocity γ vX := by
      rw [← heq]
      exact hωv
    exact ae_of_ae_map hm hv
  have hLimits : ∀ᵐ ω ∂Q.measure, ∀ᵐ γ ∂Y (0, ω),
      Clock.PhysicalClockSpeedMeaningV5.HasClockSpeed ω γ η ∧ vY = η • vX := by
    filter_upwards [Q.regular, hmap, hvY] with ω hω hm hy
    filter_upwards [hm hω, hy] with γ hx hy
    exact path_clock_ratio ω γ Λ₀ hω i hx hy hne
  have hDensity : ∀ᵐ ω ∂Q.measure, ∀ x,
      Λ⁻¹ ≤ (reduce ω).2 x ∧ (reduce ω).2 x ≤ Λ := by
    have hb := (hBound d r₀ Q).2.2
    have hb' := ae_of_ae_map Probability.measurable_reduce.aemeasurable hb
    filter_upwards [hb'] with ω hω
    exact hω.2.1
  obtain ⟨ω, hωY, hωlim, hωdens⟩ := (hY.and (hLimits.and hDensity)).exists
  haveI := hωY.1
  obtain ⟨γ, hγlim, hvel⟩ := hωlim.exists
  have hratioBounds : ∀ᶠ t : ℝ≥0 in atTop,
      Λ⁻¹ ≤ (Clock.physicalPathClock ω γ t : ℝ) / t ∧
      (Clock.physicalPathClock ω γ t : ℝ) / t ≤ Λ := by
    filter_upwards [eventually_gt_atTop (0 : ℝ≥0)] with t ht
    have hb := Clock.pathClock_bounds (clockDensity ω) (reduce ω).2.continuous
      Λ⁻¹ Λ hωdens γ t
    exact ⟨(le_div_iff₀ (NNReal.coe_pos.mpr ht)).2 hb.1,
      (div_le_iff₀ (NNReal.coe_pos.mpr ht)).2 hb.2⟩
  have hlo : Λ⁻¹ ≤ η := ge_of_tendsto hγlim (hratioBounds.mono fun _ h => h.1)
  have hhi : η ≤ Λ := le_of_tendsto hγlim (hratioBounds.mono fun _ h => h.2)
  have hηpos : 0 < η := (inv_pos.mpr (lt_of_lt_of_le zero_lt_one hΛ)).trans_le hlo
  refine ⟨η, vX, vY, hlo, hhi, ?_, hvX, hvY, hposX, hposY, rfl, ?_⟩
  · exact hLimits.mono fun _ h => h.mono fun _ hγ => hγ.1
  · rw [hvel, smul_smul, inv_mul_cancel₀ hηpos.ne', one_smul]

end EinsteinFull.Blueprint
