import EinsteinRelation.Diffusion.Basic

/-! # Time-scaled Brownian laws

Deterministic time scaling `t ↦ c * t` of continuous paths. The image of a centered
Brownian law under this scaling is again a centered Brownian law, with covariance
multiplied by `c`. This is the scaling step used by the covariance half of the
time-change identities.
-/

open MeasureTheory
open scoped BigOperators NNReal

namespace EinsteinRelation

/-- The time-scaled path `t ↦ γ (c * t)`. -/
noncomputable def timeScalePath {d : ℕ} (c : ℝ≥0) (γ : Path d) : Path d :=
  ⟨fun t => γ (c * t), γ.continuous.comp (continuous_const.mul continuous_id)⟩

/-- Time scaling is continuous on continuous-path space: it is precomposition with
the continuous map `t ↦ c * t`. -/
theorem continuous_timeScalePath {d : ℕ} (c : ℝ≥0) :
    Continuous (timeScalePath (d := d) c) := by
  have hτ : Continuous (fun t : ℝ≥0 => c * t) := continuous_const.mul continuous_id
  exact ContinuousMap.continuous_precomp (⟨fun t => c * t, hτ⟩ : C(ℝ≥0, ℝ≥0))

private theorem continuous_path_dot {d : ℕ} (ξ : Vec d) (s : ℝ≥0) :
    Continuous (fun γ : Path d => dot ξ (γ s)) := by
  unfold dot
  exact continuous_finset_sum _ fun i _ =>
    continuous_const.mul ((continuous_apply i).comp (continuous_eval_const s))

private theorem dot_smul_right_eq {d : ℕ} (c : ℝ) (ξ v : Vec d) :
    dot ξ (c • v) = c * dot ξ v := by
  simp only [dot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Scaling time by `c ≥ 0` turns a centered Brownian law into a centered Brownian law
with covariance `c • covariance`. -/
theorem IsBrownianLaw.timeScale {d : ℕ} {covariance : Mat d} {W : Measure (Path d)}
    (hW : IsBrownianLaw covariance W) {c : ℝ≥0} :
    IsBrownianLaw ((c : ℝ) • covariance) (W.map (timeScalePath c)) := by
  unfold IsBrownianLaw at hW ⊢
  obtain ⟨hprob, hsymm, hpsd, hstart, hchar⟩ := hW
  have hmeas : Measurable (timeScalePath (d := d) c) :=
    (continuous_timeScalePath c).measurable
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [Matrix.transpose_smul, hsymm]
  · intro ξ
    rw [Matrix.smul_mulVec, dot_smul_right_eq]
    exact mul_nonneg (NNReal.coe_nonneg c) (hpsd ξ)
  · have hev : Continuous fun γ : Path d => γ 0 := continuous_eval_const 0
    have hconst : Continuous fun _ : Path d => (0 : Vec d) := continuous_const
    have hclosed : MeasurableSet {γ : Path d | γ 0 = 0} :=
      (isClosed_eq hev hconst).measurableSet
    refine (ae_map_iff hmeas.aemeasurable hclosed).mpr ?_
    filter_upwards [hstart] with γ hγ
    show γ (c * 0) = 0
    rw [mul_zero]
    exact hγ
  · intro n t ξ
    have hcont : Continuous fun γ : Path d =>
        Complex.exp (Complex.I * ((∑ k, dot (ξ k) (γ (t k))) : ℂ)) :=
      Complex.continuous_exp.comp (continuous_const.mul (continuous_finset_sum _ fun k _ =>
        Complex.continuous_ofReal.comp (continuous_path_dot (ξ k) (t k))))
    have hS : (∑ k, ∑ l, (min ((c * t k : ℝ≥0) : ℝ) ((c * t l : ℝ≥0) : ℝ)) *
        dot (ξ k) (covariance.mulVec (ξ l))) =
        ∑ k, ∑ l, (min (t k) (t l) : ℝ) * dot (ξ k) (((c : ℝ) • covariance).mulVec (ξ l)) := by
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
      rw [NNReal.coe_mul, NNReal.coe_mul, ← mul_min_of_nonneg _ _ (NNReal.coe_nonneg c),
        Matrix.smul_mulVec, dot_smul_right_eq]
      ring
    rw [integral_map hmeas.aemeasurable hcont.aestronglyMeasurable]
    refine (hchar n (fun k => c * t k) ξ).trans ?_
    rw [hS]

end EinsteinRelation
