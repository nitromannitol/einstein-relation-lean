import EinsteinFull.External.DFGW.Positive

/-! # Fixed points of reversible transition operators

A fixed point of a reversible transition operator at a positive time is fixed at every time.
-/

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}

/-- An `L²` fixed point at time `t` is fixed at every time up to `t`. -/
theorem transitionOperator_fixed_of_le (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    {s t : ℝ≥0} (hst : s ≤ t) (f : Lp ℝ 2 μ)
    (hf : transitionOperator hP t f = f) : transitionOperator hP s f = f := by
  have hcontract (u : ℝ≥0) (g : Lp ℝ 2 μ) : ‖transitionOperator hP u g‖ ≤ ‖g‖ := by
    have h₁ := (transitionOperator hP u).le_opNorm g
    have h₂ := norm_transitionOperator_le_one hP u
    nlinarith [norm_nonneg g]
  have hnormt : ‖transitionOperator hP (t / 2) f‖ = ‖f‖ := by
    have heq : transitionOperator hP t f =
        transitionOperator hP (t / 2) (transitionOperator hP (t / 2) f) := by
      calc
        _ = transitionOperator hP (t / 2 + t / 2) f := by rw [add_halves]
        _ = _ := congrArg (fun A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => A f)
          (transitionOperator_add hP (t / 2) (t / 2))
    have h₁ := hcontract (t / 2) (transitionOperator hP (t / 2) f)
    have h₂ := hcontract (t / 2) f
    rw [← heq, hf] at h₁
    exact le_antisymm h₂ h₁
  have hnorms : ‖transitionOperator hP (s / 2) f‖ = ‖f‖ := by
    have hle : s / 2 ≤ t / 2 := by gcongr
    have heq : transitionOperator hP (t / 2) f =
        transitionOperator hP (t / 2 - s / 2) (transitionOperator hP (s / 2) f) := by
      calc
        _ = transitionOperator hP (t / 2 - s / 2 + s / 2) f := by
          rw [tsub_add_cancel_of_le hle]
        _ = _ := congrArg (fun A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => A f)
          (transitionOperator_add hP (t / 2 - s / 2) (s / 2))
    have h₁ := hcontract (t / 2 - s / 2) (transitionOperator hP (s / 2) f)
    rw [← heq, hnormt] at h₁
    exact le_antisymm (hcontract (s / 2) f) h₁
  have hinner : inner ℝ (transitionOperator hP s f) f = ‖f‖ ^ 2 := by
    have heq : transitionOperator hP s f =
        transitionOperator hP (s / 2) (transitionOperator hP (s / 2) f) := by
      calc
        _ = transitionOperator hP (s / 2 + s / 2) f := by rw [add_halves]
        _ = _ := congrArg (fun A : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ => A f)
          (transitionOperator_add hP (s / 2) (s / 2))
    rw [heq, inner_transitionOperator, real_inner_self_eq_norm_sq, hnorms]
  apply eq_of_norm_le_re_inner_eq_norm_sq (𝕜 := ℝ) (hcontract s f)
  simpa only [RCLike.re_to_real] using hinner

/-- A fixed point at one positive time is fixed by the entire reversible semigroup. -/
theorem transitionOperator_fixed_of_pos (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    {t : ℝ≥0} (ht : 0 < t) (f : Lp ℝ 2 μ)
    (hf : transitionOperator hP t f = f) (s : ℝ≥0) :
    transitionOperator hP s f = f := by
  have hnat (n : ℕ) : transitionOperator hP (n • t) f = f := by
    induction n with
    | zero => simp only [zero_nsmul, transitionOperator_zero, ContinuousLinearMap.id_apply]
    | succ n ih =>
      rw [succ_nsmul, transitionOperator_add]
      change transitionOperator hP (n • t) (transitionOperator hP t f) = f
      rw [hf, ih]
  have htpos : (0 : ℝ) < t := by exact_mod_cast ht
  obtain ⟨n, hn⟩ := exists_nat_gt ((s : ℝ) / (t : ℝ))
  have hst : s ≤ n • t := by
    apply NNReal.coe_le_coe.mp
    simp only [nsmul_eq_mul, NNReal.coe_mul, NNReal.coe_natCast]
    exact le_of_lt ((div_lt_iff₀ htpos).mp hn)
  exact transitionOperator_fixed_of_le hP hst f (hnat n)

end EinsteinFull.External.DFGW
