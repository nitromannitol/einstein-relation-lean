import EinsteinFull.External.DFGW.DynkinStationary
import EinsteinFull.External.DFGW.ReflectionDrift
import EinsteinFull.External.DFGW.ObservableEnergyL2

/-! # Reflection orthogonality for Dynkin martingales

Reversibility makes a state-observable increment orthogonal to an integrated state observable.
The Dynkin increment therefore has a Pythagorean second-moment identity.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A state-observable increment is orthogonal to an integrated state observable. -/
theorem integral_L2_increment_mul_time_integral_eq_zero
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (f g : Lp ℝ 2 μ) (t : ℝ≥0) :
    (∫ η : C(ℝ, S), (f (η t) - f (η 0)) *
      (∫ u in (0 : ℝ)..t, g (η u)) ∂P) = 0 := by
  have hev (u : ℝ) : MeasurePreserving (fun η : C(ℝ, S) => η u) P μ :=
    ⟨(continuous_eval_const u).measurable, hP.marginal u⟩
  have hF : MemLp (fun η : C(ℝ, S) => f (η t) - f (η 0)) 2 P :=
    ((Lp.memLp f).comp_measurePreserving (hev t)).sub
      ((Lp.memLp f).comp_measurePreserving (hev 0))
  have hG := (time_integral_memLp_and_sq_le hP g (Lp.memLp g) t.coe_nonneg).1
  have hint := hF.integrable_mul hG
  let H : C(ℝ, S) → ℝ := fun η => (f (η t) - f (η 0)) *
    (∫ u in (0 : ℝ)..t, g (η u))
  have hm : AEStronglyMeasurable H (P.map (Draft.dfgwRefl ((t : ℝ) / 2))) := by
    rw [hP.reversible]
    exact hint.aestronglyMeasurable
  have he : (∫ η, H η ∂P) = -(∫ η, H η ∂P) := by
    calc
      _ = ∫ η, H η ∂P.map (Draft.dfgwRefl ((t : ℝ) / 2)) := by rw [hP.reversible]
      _ = ∫ η, H (Draft.dfgwRefl ((t : ℝ) / 2) η) ∂P :=
        integral_map (measurable_refl _).aemeasurable hm
      _ = ∫ η, -H η ∂P := by
        apply integral_congr_ae
        filter_upwards with η
        dsimp only [H]
        rw [intervalIntegral_observable_refl]
        have h1 : Draft.dfgwRefl ((t : ℝ) / 2) η t = η 0 := by
          change η (2 * ((t : ℝ) / 2) - t) = η 0
          congr 1; ring
        have h0 : Draft.dfgwRefl ((t : ℝ) / 2) η 0 = η t := by
          change η (2 * ((t : ℝ) / 2) - 0) = η t
          congr 1; ring
        rw [h1, h0]
        ring
      _ = _ := integral_neg _
  exact (eq_neg_iff_add_eq_zero.mp he) |> fun h => by linarith

/-- The Dynkin increment variance is the sum of the state and generator integral variances. -/
theorem integral_dynkin_increment_sq_eq_energy_add (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : (transitionSemigroup hP).generatorDomain) (t : ℝ≥0) :
    (∫ η, (dynkinProcess hP f t η - dynkinProcess hP f 0 η) ^ 2 ∂P) =
      2 * (‖(f : Lp ℝ 2 μ)‖ ^ 2 -
        inner ℝ (f : Lp ℝ 2 μ) (transitionOperator hP t (f : Lp ℝ 2 μ))) +
      ∫ η, (∫ u in (0 : ℝ)..t, (transitionSemigroup hP).generator f (η u)) ^ 2 ∂P := by
  let F : Lp ℝ 2 μ := f
  let g := (transitionSemigroup hP).generator f
  let A : C(ℝ, S) → ℝ := fun η => F (η t) - F (η 0)
  let B : C(ℝ, S) → ℝ := fun η => ∫ u in (0 : ℝ)..t, g (η u)
  have hev (u : ℝ) : MeasurePreserving (fun η : C(ℝ, S) => η u) P μ :=
    ⟨(continuous_eval_const u).measurable, hP.marginal u⟩
  have hA : MemLp A 2 P := ((Lp.memLp F).comp_measurePreserving (hev t)).sub
    ((Lp.memLp F).comp_measurePreserving (hev 0))
  have hB : MemLp B 2 P := (time_integral_memLp_and_sq_le hP g (Lp.memLp g) t.coe_nonneg).1
  have horth : (∫ η, A η * B η ∂P) = 0 :=
    integral_L2_increment_mul_time_integral_eq_zero hP F g t
  have heq : (fun η => (dynkinProcess hP f t η - dynkinProcess hP f 0 η) ^ 2) =
      fun η => A η ^ 2 + B η ^ 2 - 2 * (A η * B η) := by
    funext η
    simp only [dynkinProcess, NNReal.coe_zero, intervalIntegral.integral_same, sub_zero, A, B, F, g]
    ring
  have hsum : Integrable (fun η => A η ^ 2 + B η ^ 2) P :=
    hA.integrable_sq.add hB.integrable_sq
  have hcross : Integrable (fun η => 2 * (A η * B η)) P :=
    (hA.integrable_mul hB).const_mul 2
  rw [heq, integral_sub hsum hcross, integral_add hA.integrable_sq hB.integrable_sq,
    integral_const_mul, horth]
  simp only [mul_zero, sub_zero]
  rw [integral_L2_observable_increment_sq hP F t]

end EinsteinFull.External.DFGW
