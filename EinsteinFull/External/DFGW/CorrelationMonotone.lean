import EinsteinFull.External.DFGW.Positive

/-! # Monotonicity of reversible correlations

The autocorrelation of a square-integrable observable decreases with elapsed time for a
reversible Markov semigroup.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- Reversible transition autocorrelations decrease with time. -/
theorem antitone_inner_transitionOperator (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (f : Lp ℝ 2 μ) : Antitone (fun t : ℝ≥0 => inner ℝ f (transitionOperator hP t f)) := by
  have hnorm (t : ℝ≥0) : inner ℝ f (transitionOperator hP t f) =
      ‖transitionOperator hP (t / 2) f‖ ^ 2 := by
    have heq : transitionOperator hP t f =
        transitionOperator hP (t / 2) (transitionOperator hP (t / 2) f) := by
      calc
        _ = transitionOperator hP (t / 2 + t / 2) f := by rw [add_halves]
        _ = _ := congrArg (fun A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => A f)
          (transitionOperator_add hP (t / 2) (t / 2))
    rw [heq, ← inner_transitionOperator, real_inner_self_eq_norm_sq]
  intro s t hst
  change inner ℝ f (transitionOperator hP t f) ≤ inner ℝ f (transitionOperator hP s f)
  rw [hnorm, hnorm]
  have hle : s / 2 ≤ t / 2 := by gcongr
  have heq : transitionOperator hP (t / 2) f =
      transitionOperator hP (t / 2 - s / 2) (transitionOperator hP (s / 2) f) := by
    calc
      _ = transitionOperator hP (t / 2 - s / 2 + s / 2) f := by
        rw [tsub_add_cancel_of_le hle]
      _ = _ := congrArg (fun A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => A f)
        (transitionOperator_add hP (t / 2 - s / 2) (s / 2))
  have hcontract : ‖transitionOperator hP (t / 2) f‖ ≤
      ‖transitionOperator hP (s / 2) f‖ := by
    rw [heq]
    have h₁ := (transitionOperator hP (t / 2 - s / 2)).le_opNorm
      (transitionOperator hP (s / 2) f)
    have h₂ := norm_transitionOperator_le_one hP (t / 2 - s / 2)
    nlinarith [norm_nonneg (transitionOperator hP (s / 2) f)]
  nlinarith [norm_nonneg (transitionOperator hP (t / 2) f),
    norm_nonneg (transitionOperator hP (s / 2) f)]

end EinsteinFull.External.DFGW
