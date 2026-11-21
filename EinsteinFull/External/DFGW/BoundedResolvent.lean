import EinsteinFull.External.DFGW.BoundedTransition
import EinsteinFull.External.DFGW.Resolvent
import Mathlib.MeasureTheory.Function.LpOrder

/-! # Boundedness of the resolvent

The Laplace resolvent preserves essentially bounded observables.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

private instance : IsOrderedModule ℝ (Lp ℝ 2 μ) :=
  IsOrderedModule.of_smul_nonneg fun a ha f hf => by
    rw [← Lp.coeFn_nonneg] at hf ⊢
    filter_upwards [hf, Lp.coeFn_smul a f] with x hx hax
    change 0 ≤ (a • f) x
    rw [hax]
    exact mul_nonneg ha hx

/-- The resolvent of an essentially bounded observable is essentially bounded. -/
theorem transitionResolvent_ae_norm_le (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (lam : MarkovProcess.Semigroup.PositiveShift) (f : Lp ℝ 2 μ) (C : ℝ)
    (hf : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    ∀ᵐ x ∂μ, ‖transitionResolvent hP lam f x‖ ≤ (lam : ℝ)⁻¹ * C := by
  let : IsProbabilityMeasure μ := hP.invariant_probability
  let c : Lp ℝ 2 μ := (memLp_const C).toLp (fun _ : S => C)
  have hc : ∀ᵐ x ∂μ, c x = C := MemLp.coeFn_toLp (memLp_const C)
  let A := transitionSemigroup hP
  have hbound : ∀ t : ℝ≥0, -c ≤ A t f ∧ A t f ≤ c := by
    intro t
    have ht := transitionSemigroup_ae_norm_le hP t f C hf
    constructor
    · rw [← Lp.coeFn_le]
      filter_upwards [ht, hc, Lp.coeFn_neg c] with x hx hcx hn
      change (-c) x ≤ A t f x
      simp only [Pi.neg_apply] at hn
      rw [hn, hcx]
      exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hx)).1
    · rw [← Lp.coeFn_le]
      filter_upwards [ht, hc] with x hx hcx
      change A t f x ≤ c x
      rw [hcx]
      exact (abs_le.mp (by simpa only [Real.norm_eq_abs] using hx)).2
  have hint : IntegrableOn (fun t : ℝ => Real.exp (-(lam : ℝ) * t) • c) (Set.Ioi 0) :=
    (exp_neg_integrableOn_Ioi 0 lam.2).smul_const c
  have hupper : transitionResolvent hP lam f ≤ (lam : ℝ)⁻¹ • c := by
    rw [transitionResolvent, A.resolvent_apply]
    have h := integral_mono (A.integrableOn_laplaceIntegrand lam.2 f) hint
      (fun t => by
        rw [A.laplaceIntegrand_apply]
        exact smul_le_smul_of_nonneg_left (hbound (Real.toNNReal t)).2 (Real.exp_pos _).le)
    rw [integral_smul_const, MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero lam.2] at h
    exact h
  have hlower : -((lam : ℝ)⁻¹ • c) ≤ transitionResolvent hP lam f := by
    rw [transitionResolvent, A.resolvent_apply]
    have hintneg : IntegrableOn (fun t : ℝ => Real.exp (-(lam : ℝ) * t) • (-c))
        (Set.Ioi 0) := (exp_neg_integrableOn_Ioi 0 lam.2).smul_const (-c)
    have h := integral_mono hintneg (A.integrableOn_laplaceIntegrand lam.2 f)
      (fun t => by
        rw [A.laplaceIntegrand_apply]
        exact smul_le_smul_of_nonneg_left (hbound (Real.toNNReal t)).1 (Real.exp_pos _).le)
    rw [integral_smul_const, MarkovProcess.Semigroup.StronglyContinuousContractionSemigroup.integral_exp_neg_mul_Ioi_zero lam.2, smul_neg] at h
    exact h
  rw [← Lp.coeFn_le] at hupper hlower
  filter_upwards [hupper, hlower, hc, Lp.coeFn_smul (lam : ℝ)⁻¹ c,
    Lp.coeFn_neg ((lam : ℝ)⁻¹ • c)] with x hu hl hcx hs hn
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, hcx] at hu
  change (-((lam : ℝ)⁻¹ • c)) x ≤ transitionResolvent hP lam f x at hl
  rw [hn] at hl
  simp only [Pi.neg_apply] at hl
  rw [hs, hcx] at hl
  simpa only [Real.norm_eq_abs] using (abs_le.mpr ⟨hl, hu⟩)

end EinsteinFull.External.DFGW
