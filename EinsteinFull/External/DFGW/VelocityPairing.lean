import EinsteinFull.External.DFGW.ForwardPairing
import EinsteinFull.External.DFGW.Velocity

/-! # Pairings with the mean forward velocity

The strong `L¹` forward-velocity limit passes through bounded initial-state observables.
-/

open MeasureTheory ProbabilityTheory Filter EinsteinRelation
open scoped NNReal Topology

namespace EinsteinFull.External.DFGW

variable {S : Type*} [TopologicalSpace S] [MeasurableSpace S] [BorelSpace S]
variable {d : ℕ} {P : Measure C(ℝ, S)} {μ : Measure S} {T : ℝ≥0 → Kernel S S}
variable {X : ℝ → ℝ → C(ℝ, S) → Vec d} {Y : C(ℝ, S) → Path d}

/-- Bounded initial-state observables may be paired with the `L¹` forward-velocity limit. -/
theorem tendsto_increment_pairing (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (i : Fin d) (f : S → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    Tendsto (fun δ : ℝ => δ⁻¹ * ∫ η, X 0 δ η i * f (η 0) ∂P)
      (𝓝[>] 0) (𝓝 (∫ x, φ x i * f x ∂μ)) := by
  let : IsProbabilityMeasure P := hP.probability
  let : IsProbabilityMeasure μ := hP.invariant_probability
  obtain ⟨C, hC⟩ := hfb
  let V : C(ℝ, S) → Vec d := fun η => φ (η 0)
  let U : ℝ → C(ℝ, S) → Vec d := fun δ η =>
    δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η
  let F : C(ℝ, S) → ℝ := fun η => f (η 0)
  let L : Vec d →L[ℝ] ℝ := ContinuousLinearMap.proj i
  let B : ℝ := |C| * ‖L‖
  have hV : Integrable V P := by
    have hm : AEStronglyMeasurable φ (P.map (fun η : C(ℝ, S) => η 0)) := by
      rw [hP.marginal]
      exact (hφ.integrable one_le_two).aestronglyMeasurable
    apply (integrable_map_measure hm (continuous_eval_const (0 : ℝ)).measurable.aemeasurable).1
    rw [hP.marginal]
    exact hφ.integrable one_le_two
  have hU (δ : ℝ) : Integrable (U δ) P := by
    change Integrable (δ⁻¹ • P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) P
    exact integrable_condExp.smul δ⁻¹
  have hFm : Measurable F := hf.comp (continuous_eval_const 0).measurable
  have hF (η : C(ℝ, S)) : ‖F η‖ ≤ |C| := by
    have h : ‖F η‖ ≤ C := by simpa only [F, Real.norm_eq_abs] using hC (η 0)
    exact h.trans (le_abs_self C)
  have hpairU (δ : ℝ) : Integrable (fun η => U δ η i * F η) P :=
    (hU δ).eval i |>.mul_bdd hFm.aestronglyMeasurable (ae_of_all P hF)
  have hpairV : Integrable (fun η => V η i * F η) P :=
    hV.eval i |>.mul_bdd hFm.aestronglyMeasurable (ae_of_all P hF)
  have hbound (δ : ℝ) :
      ‖(∫ η, U δ η i * F η ∂P) - (∫ η, V η i * F η ∂P)‖ ≤
        B * ∫ η, ‖U δ η - V η‖ ∂P := by
    have hdiff : (∫ η, U δ η i * F η ∂P) - (∫ η, V η i * F η ∂P) =
        ∫ η, (U δ η i - V η i) * F η ∂P := by
      rw [← integral_sub (hpairU δ) hpairV]
      apply integral_congr_ae
      exact ae_of_all P fun η => by ring
    rw [hdiff, ← integral_const_mul]
    calc
      ‖∫ η, (U δ η i - V η i) * F η ∂P‖ ≤
          ∫ η, ‖(U δ η i - V η i) * F η‖ ∂P := norm_integral_le_integral_norm _
      _ ≤ ∫ η, B * ‖U δ η - V η‖ ∂P := by
        have hd : Integrable (fun η => (U δ η i - V η i) * F η) P := by
          have h := ((hU δ).sub hV).eval i |>.mul_bdd hFm.aestronglyMeasurable (ae_of_all P hF)
          simpa only [Pi.sub_apply] using h
        apply integral_mono_ae hd.norm (((hU δ).sub hV).norm.const_mul B)
        filter_upwards with η
        have hL : ‖U δ η i - V η i‖ ≤ ‖L‖ * ‖U δ η - V η‖ := by
          simpa only [L, ContinuousLinearMap.proj_apply, Pi.sub_apply] using
            L.le_opNorm (U δ η - V η)
        rw [norm_mul]
        calc
          ‖U δ η i - V η i‖ * ‖F η‖ ≤
              (‖L‖ * ‖U δ η - V η‖) * |C| :=
            mul_le_mul hL (hF η) (norm_nonneg _) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
          _ = B * ‖U δ η - V η‖ := by simp only [B]; ring
  have hpairlim : Tendsto (fun δ : ℝ => ∫ η, U δ η i * F η ∂P)
      (𝓝[>] 0) (𝓝 (∫ η, V η i * F η ∂P)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero' (Filter.Eventually.of_forall fun δ => norm_nonneg _)
      (Filter.Eventually.of_forall hbound)
    simpa only [mul_zero, U, V] using hlim.const_mul B
  have hvmap : (∫ η, V η i * F η ∂P) = ∫ x, φ x i * f x ∂μ := by
    have hm : AEStronglyMeasurable (fun x => φ x i * f x) μ := by
      have hb : ∀ x, ‖f x‖ ≤ |C| := fun x => by
        have hx : ‖f x‖ ≤ C := by simpa only [Real.norm_eq_abs] using hC x
        exact hx.trans (le_abs_self C)
      exact ((hφ.integrable one_le_two).eval i |>.mul_bdd hf.aestronglyMeasurable
        (ae_of_all μ hb)).aestronglyMeasurable
    have h := integral_map (μ := P) (continuous_eval_const (0 : ℝ)).measurable.aemeasurable
      (f := fun x => φ x i * f x) (by rw [hP.marginal]; exact hm)
    rw [hP.marginal] at h
    exact h.symm
  rw [hvmap] at hpairlim
  apply hpairlim.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have hp := integral_condExp_increment_mul_eval hP hX hδ.le i f hf ⟨C, hC⟩
  calc
    (∫ η, U δ η i * F η ∂P) =
        δ⁻¹ * ∫ η, (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η i * f (η 0) ∂P := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all P fun η => by simp only [U, F, Pi.smul_apply, smul_eq_mul]; ring
    _ = δ⁻¹ * ∫ η, X 0 δ η i * f (η 0) ∂P := by rw [hp]

/-- The mean velocity pairs with the increment of a bounded observable by reflection. -/
theorem tendsto_increment_observable_difference (hP : Draft.IsDFGWTrajectoryProcess P μ T)
    (hX : Draft.IsDFGWTrajectoryFamily P X Y) (φ : S → Vec d) (hφ : MemLp φ 2 μ)
    (hlim : Tendsto (fun δ : ℝ =>
      ∫ η, ‖δ⁻¹ • (P[X 0 δ | Draft.dfgwCoordSigma (Set.Iic 0)]) η - φ (η 0)‖ ∂P)
      (𝓝[>] 0) (𝓝 0))
    (i : Fin d) (f : S → ℝ) (hf : Measurable f) (hfb : ∃ C, ∀ x, |f x| ≤ C) :
    Tendsto (fun δ : ℝ => δ⁻¹ * ∫ η, X 0 δ η i * (f (η δ) - f (η 0)) ∂P)
      (𝓝[>] 0) (𝓝 (-2 * ∫ x, φ x i * f x ∂μ)) := by
  have h := (tendsto_increment_pairing hP hX φ hφ hlim i f hf hfb).const_mul (-2)
  apply h.congr'
  filter_upwards [self_mem_nhdsWithin] with δ hδ
  have he := integral_increment_mul_eval_difference hP hX hδ.le i f hf hfb
  have he' : (∫ η, X 0 δ η i * (f (η δ) - f (η 0)) ∂P) =
      -(2 * ∫ η, X 0 δ η i * f (η 0) ∂P) := by linarith
  rw [he']
  ring

end EinsteinFull.External.DFGW
