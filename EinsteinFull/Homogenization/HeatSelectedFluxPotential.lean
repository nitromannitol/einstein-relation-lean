import EinsteinFull.Homogenization.HeatSelectedFluxExistence
import EinsteinFull.Homogenization.HeatPotentialWeakGradient
import EinsteinFull.Calculus.C2BallPoincareFromPDE
import EinsteinRelation.Correctors.PairedParabolicEquation
import EinsteinRelation.Correctors.WeakGradientCentering

/-!
# The potential of the heat-selected flux gradient

The truncations of the heat formula (6.7) of Armstrong, Kuusi and Mourrat, *Quantitative
Stochastic Homogenization and Large-Scale Regularity*, are the weak gradients of the truncated
first-derivative formulas `∫_{1/(p+1)}^{p+1} (∂ⱼΦ_t * g_k - ∂ₖΦ_t * g_j) dt`. Normalized by their
averages over the unit ball, these potentials are Cauchy in `L²` on every ball by the Poincaré
inequality, and their selected limit is a potential of the heat-selected flux gradient.
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace EinsteinFull.Homogenization

open EinsteinRelation EinsteinRelation.Correctors EinsteinRelation.External.AKM
open EinsteinRelation.Correctors.HeatSelectedSkewMeaning

variable {d : ℕ}

theorem isFiniteMeasure_restrict_ball (ρ : ℝ) :
    IsFiniteMeasure (volume.restrict (ball (0 : Vec d) ρ)) :=
  isFiniteMeasure_restrict.mpr (volume_ball_zero_lt_top ρ).ne

/-- Testing against a compactly supported continuous function is continuous for `L²`
convergence on a ball containing its support. -/
theorem tendsto_integral_mul_of_eLpNorm {u : Vec d → ℝ} {un : ℕ → Vec d → ℝ}
    (hu : ∀ R : ℝ, MemLp u 2 (volume.restrict (ball 0 R)))
    (hun : ∀ n (R : ℝ), MemLp (un n) 2 (volume.restrict (ball 0 R)))
    {φ : Vec d → ℝ} (hφ : Continuous φ) (hφc : HasCompactSupport φ) {ρ : ℝ}
    (hρ : tsupport φ ⊆ ball 0 ρ)
    (hconv : Tendsto (fun n => eLpNorm (fun x => un n x - u x) 2
      (volume.restrict (ball 0 ρ))) atTop (𝓝 0)) :
    Tendsto (fun n => ∫ x, un n x * φ x) atTop (𝓝 (∫ x, u x * φ x)) := by
  have := isFiniteMeasure_restrict_ball (d := d) ρ
  obtain ⟨M, hM⟩ := hφc.exists_bound_of_continuous hφ
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hM 0)
  set V : ℝ≥0∞ := (volume.restrict (ball (0 : Vec d) ρ)) univ ^ (1 / (1 : ℝ≥0∞).toReal -
    1 / (2 : ℝ≥0∞).toReal) with hV
  have hVfin : V ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by norm_num) (measure_ne_top _ _)
  have hint : ∀ n, Integrable (fun x => un n x * φ x) volume := fun n => by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_of_memLp_ball (hun n)).integrable_smul_right_of_hasCompactSupport hφ hφc
  have huint : Integrable (fun x => u x * φ x) volume := by
    simpa only [smul_eq_mul] using
      (locallyIntegrable_of_memLp_ball hu).integrable_smul_right_of_hasCompactSupport hφ hφc
  have hbound : ∀ n, ‖(∫ x, un n x * φ x) - ∫ x, u x * φ x‖ ≤
      M * (eLpNorm (fun x => un n x - u x) 2 (volume.restrict (ball 0 ρ)) * V).toReal := by
    intro n
    have hF2 : MemLp (fun x => un n x - u x) 2 (volume.restrict (ball 0 ρ)) :=
      (hun n ρ).sub (hu ρ)
    have hF := hF2.aestronglyMeasurable
    rw [← integral_sub (hint n) huint]
    have hzero : ∀ x ∉ ball (0 : Vec d) ρ, un n x * φ x - u x * φ x = 0 := fun x hx => by
      rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hρ h)), mul_zero, mul_zero, sub_zero]
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero hzero]
    calc ‖∫ x in ball 0 ρ, (un n x * φ x - u x * φ x)‖
        ≤ ∫ x in ball 0 ρ, ‖un n x * φ x - u x * φ x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x in ball 0 ρ, M * ‖un n x - u x‖ := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ => norm_nonneg _)
            ((hF2.integrable (by norm_num)).norm.const_mul M)
            (Filter.Eventually.of_forall fun x => ?_)
          simp only
          rw [← sub_mul, norm_mul, mul_comm]
          exact mul_le_mul_of_nonneg_right (hM x) (norm_nonneg _)
      _ = M * (eLpNorm (fun x => un n x - u x) 1 (volume.restrict (ball 0 ρ))).toReal := by
          rw [integral_const_mul, integral_norm_eq_lintegral_enorm hF,
            eLpNorm_one_eq_lintegral_enorm hF]
      _ ≤ M * (eLpNorm (fun x => un n x - u x) 2 (volume.restrict (ball 0 ρ)) * V).toReal :=
          mul_le_mul_of_nonneg_left (ENNReal.toReal_mono
            (ENNReal.mul_ne_top hF2.eLpNorm_ne_top hVfin)
            (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (by norm_num) hF)) hM0
  have hlim : Tendsto (fun n => M * (eLpNorm (fun x => un n x - u x) 2
      (volume.restrict (ball 0 ρ)) * V).toReal) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n => eLpNorm (fun x => un n x - u x) 2
        (volume.restrict (ball 0 ρ)) * V) atTop (𝓝 0) := by
      simpa using ENNReal.Tendsto.mul_const hconv (Or.inr hVfin)
    have h2 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simpa using h2.const_mul M
  rw [tendsto_iff_norm_sub_tendsto_zero]
  exact squeeze_zero (fun _ => norm_nonneg _) hbound hlim

/-- **Closure of weak partial derivatives** under `L²` convergence on balls. -/
theorem hasWeakPartialDerivative_of_tendsto {u v : Vec d → ℝ} {un vn : ℕ → Vec d → ℝ}
    (i : Fin d) (hn : ∀ n, HasWeakPartialDerivative univ i (un n) (vn n))
    (hu : ∀ R : ℝ, MemLp u 2 (volume.restrict (ball 0 R)))
    (hv : ∀ R : ℝ, MemLp v 2 (volume.restrict (ball 0 R)))
    (hun : ∀ n (R : ℝ), MemLp (un n) 2 (volume.restrict (ball 0 R)))
    (hvn : ∀ n (R : ℝ), MemLp (vn n) 2 (volume.restrict (ball 0 R)))
    (hconvu : ∀ R : ℝ, Tendsto (fun n => eLpNorm (fun x => un n x - u x) 2
      (volume.restrict (ball 0 R))) atTop (𝓝 0))
    (hconvv : ∀ R : ℝ, Tendsto (fun n => eLpNorm (fun x => vn n x - v x) 2
      (volume.restrict (ball 0 R))) atTop (𝓝 0)) :
    HasWeakPartialDerivative univ i u v := by
  refine ⟨locallyIntegrableOn_univ.mpr (locallyIntegrable_of_memLp_ball hu),
    locallyIntegrableOn_univ.mpr (locallyIntegrable_of_memLp_ball hv), fun ψ hψt => ?_⟩
  have hψ : IsSmoothCompact ψ := ⟨hψt.1, hψt.2.1⟩
  have hiψ := hψ.coordinateDerivative i
  obtain ⟨ρ, hρ⟩ := exists_euclideanNorm_le_of_hasCompactSupport hψ.2
  have hsub : tsupport ψ ⊆ ball 0 (ρ + 1) := fun x hx => by
    change euclideanNorm (x - 0) < ρ + 1
    rw [sub_zero]
    linarith [hρ x hx]
  have hsub' : tsupport (coordinateDerivative i ψ) ⊆ ball 0 (ρ + 1) :=
    (tsupport_fderiv_apply_subset ℝ _).trans hsub
  have hl := tendsto_integral_mul_of_eLpNorm hu hun hiψ.1.continuous hiψ.2 hsub' (hconvu _)
  have hr := (tendsto_integral_mul_of_eLpNorm hv hvn hψ.1.continuous hψ.2 hsub (hconvv _)).neg
  rw [Measure.restrict_univ]
  refine tendsto_nhds_unique hl (hr.congr fun n => ?_)
  have h := (hn n).2.2 ψ hψt
  rw [Measure.restrict_univ] at h
  exact h.symm

end EinsteinFull.Homogenization
