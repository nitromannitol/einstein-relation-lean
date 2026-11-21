import EinsteinFull.External.DFGW.AutocorrelationDistance
import EinsteinFull.External.DFGW.SemigroupFixedPoints

/-! # Fixed observables along stationary paths

A fixed point of a positive-time transition operator is constant along each trajectory at any
prescribed pair of times, almost surely.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- A transition fixed point has equal values at any two fixed trajectory times almost surely. -/
theorem ae_eval_eq_of_transitionOperator_fixed
    (hP : Draft.IsDFGWTrajectoryProcess P μ T) (f : Lp ℝ 2 μ)
    {t : ℝ≥0} (ht : 0 < t) (hf : transitionOperator hP t f = f) (u v : ℝ) :
    ∀ᵐ η ∂P, f (η u) = f (η v) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  have heval (s : ℝ) : MeasurePreserving (fun η : C(ℝ, S) => η s) P μ :=
    ⟨(continuous_eval_const s).measurable, hP.marginal s⟩
  have hmem (s : ℝ) : MemLp (fun η : C(ℝ, S) => f (η s)) 2 P :=
    (Lp.memLp f).comp_measurePreserving (heval s)
  have hsq (s : ℝ) : Integrable (fun η : C(ℝ, S) => (f (η s)) ^ 2) P :=
    (hmem s).integrable_sq
  have hmul : Integrable (fun η : C(ℝ, S) => f (η u) * f (η v)) P :=
    (hmem u).integrable_mul (hmem v)
  have heq (s : ℝ) : (∫ η : C(ℝ, S), (f (η s)) ^ 2 ∂P) = ‖f‖ ^ 2 := by
    calc
      _ = ∫ x, (f x) ^ 2 ∂μ := by
        have hm := integral_map (μ := P) (continuous_eval_const s).measurable.aemeasurable
          (f := fun x => (f x) ^ 2) (by
            rw [hP.marginal]
            exact (Lp.memLp f).integrable_sq.aestronglyMeasurable)
        rw [hP.marginal] at hm
        exact hm.symm
      _ = ‖f‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq, L2.inner_def]
        apply integral_congr_ae
        filter_upwards with x
        simp only [RCLike.inner_apply, starRingEnd_apply, star_trivial, pow_two]
  have hc := integral_eval_mul_eval_eq_autocorrelation hP f (Lp.memLp f) u v
  have hto : (Lp.memLp f).toLp (fun x => f x) = f := Lp.toLp_coeFn f (Lp.memLp f)
  rw [hto, transitionOperator_fixed_of_pos hP ht f hf, real_inner_self_eq_norm_sq] at hc
  have hzero : (∫ η : C(ℝ, S), (f (η u) - f (η v)) ^ 2 ∂P) = 0 := by
    have hid : (fun η : C(ℝ, S) => (f (η u) - f (η v)) ^ 2) =
        fun η => (f (η u)) ^ 2 + (f (η v)) ^ 2 - 2 * (f (η u) * f (η v)) := by
      funext η
      ring
    rw [hid]
    change (∫ η : C(ℝ, S), ((fun η : C(ℝ, S) => (f (η u)) ^ 2) +
      (fun η : C(ℝ, S) => (f (η v)) ^ 2)) η - 2 * (f (η u) * f (η v)) ∂P) = 0
    rw [integral_sub ((hsq u).add (hsq v)) (hmul.const_mul 2)]
    simp only [Pi.add_apply]
    rw [integral_add (hsq u) (hsq v), integral_const_mul, heq u, heq v, hc]
    ring
  have hnonneg := (integral_eq_zero_iff_of_nonneg_ae
    (ae_of_all P fun η => sq_nonneg (f (η u) - f (η v))) ((hmem u).sub (hmem v)).integrable_sq).1 hzero
  filter_upwards [hnonneg] with η hη
  exact sub_eq_zero.mp ((sq_eq_zero_iff).1 hη)

end EinsteinFull.External.DFGW
